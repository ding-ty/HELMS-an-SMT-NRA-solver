"""Read-only checks of the selected paper observations and retained evidence."""

import argparse
from collections import Counter, defaultdict
import csv
from decimal import Decimal, InvalidOperation
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
from pathlib import PurePosixPath
import sys
import tarfile


METHODS = ('HELMS', '2D-LS', 'V1', 'V2', 'V3', 'V4', 'V5',
           'LS-WL', 'LiMbS', 'OpenCAD')
CASE_COUNTS = {'SMTLIB': 2139, 'RandInst': 100, 'SpecInst': 21}
FIELDS = ('observation_id', 'benchmark', 'case_id', 'solver', 'measurement_id',
          'status', 'solved', 'solve_seconds', 'worker_wall_seconds',
          'external_elapsed_seconds', 'validation_seconds', 'stage',
          'failure_kind', 'input_sha256', 'expected_status', 'within_60s')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def file_digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(chunk)
    return result.hexdigest()


def local_path(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root), 'A path leaves the repository: ' + str(relative))
    return path


def load_json(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def read_csv(path):
    with path.open(encoding='utf-8-sig', newline='') as stream:
        reader = csv.DictReader(stream)
        rows = list(reader)
    return reader.fieldnames, rows


def answer(row):
    return {'sat_verified': 'sat', 'unsat_reported': 'unsat'}.get(
        row['status'], row['status'])


def decimal_time(value):
    try:
        result = Decimal(value)
    except (InvalidOperation, TypeError, ValueError):
        return None
    return result if result.is_finite() else None


def within_limit(row, limit):
    elapsed = decimal_time(row['solve_seconds'])
    return (row['solved'].lower() == 'true' and answer(row) in ('sat', 'unsat')
            and elapsed is not None and Decimal(0) <= elapsed <= limit)


def verify_file(root, relative, specification):
    path = local_path(root, relative)
    require(path.is_file(), 'Missing file: ' + relative)
    require(path.stat().st_size == int(specification['bytes']),
            'Byte count differs: ' + relative)
    require(file_digest(path) == specification['sha256'],
            'SHA-256 differs: ' + relative)


def verify_manifest(root):
    manifest = load_json(root / 'ARTIFACT_MANIFEST.json')
    known = manifest['files']
    actual = {path.relative_to(root).as_posix() for path in root.rglob('*')
              if path.is_file() and path.name != 'ARTIFACT_MANIFEST.json'
              and '__pycache__' not in path.parts}
    require(actual == set(known), 'Public file inventory differs from the manifest')
    for relative, specification in known.items():
        verify_file(root, relative, specification)
    return len(known)


def canonical_source_check(row, original, source, trace):
    expected_solver = original.get('solver') or original.get('method')
    expected_solver = {'LIMBS': 'LiMbS'}.get(expected_solver, expected_solver)
    expected_status = original.get('expected_status', '')
    if trace.get('reference_status'):
        expected_status = trace['reference_status']['value']
    expected = {
        'case_id': original['case_id'],
        'input_sha256': original['input_sha256'],
        'status': original['status'],
        'solve_seconds': original.get('solve_seconds', ''),
        'solver': expected_solver,
        'solved': (original['solved'].lower() if 'solved' in original else
                   str(original['status'] in ('sat_verified', 'unsat_reported')).lower()),
        'benchmark': source.get('benchmark_override') or original.get('benchmark'),
        'worker_wall_seconds': original.get(
            'worker_wall_seconds', original.get('attempt_wall_seconds', '')),
        'external_elapsed_seconds': original.get(
            'external_solver_finished_observed_seconds', ''),
        'validation_seconds': original.get('validation_seconds', ''),
        'expected_status': expected_status,
        'stage': original.get('stage', ''),
        'failure_kind': original.get('failure_kind', ''),
    }
    for field, value in expected.items():
        require(row[field] == value,
                'Source value differs: ' + row['observation_id'] + ':' + field)
    require(row['measurement_id'] == trace['measurement_id'],
            'Measurement identity differs from provenance')
    require(row['input_sha256'] == trace['input_sha256'],
            'Input identity differs from provenance')
    if original.get('job_key'):
        require(trace['evidence']['job_key'] == original['job_key'],
                'Recorded job identity differs')
    if original.get('final_json_sha256'):
        require(trace['evidence']['final_record_sha256'] == original['final_json_sha256'],
                'Recorded final-result identity differs')


def verify_sources(root, rows, traces, sources):
    by_id = {row['observation_id']: row for row in rows}
    trace_by_origin = {(trace['source_id'], int(trace['source_row'])): trace
                       for trace in traces}
    require(len(trace_by_origin) == len(traces), 'Duplicate source-row provenance')
    require(set(trace['observation_id'] for trace in traces) == set(by_id),
            'Provenance and selected observation identities differ')
    checked = set()
    for source_id, source in sources.items():
        require(int(source['original_records']) >= int(source['records']),
                'Selected source count exceeds original source count')
        for key in ('original_sha256', 'original_bytes'):
            require(key in source, 'Missing original source identity: ' + key)
        relative = source['selected_path']
        verify_file(root, relative, source)
        with gzip.open(local_path(root, relative), 'rt', encoding='utf-8-sig',
                       newline='') as stream:
            reader = csv.DictReader(stream)
            require(reader.fieldnames == ['source_row'] + source['columns'],
                    'Original source field order differs: ' + source_id)
            native_rows = list(reader)
        require(len(native_rows) == int(source['records']),
                'Selected source record count differs: ' + source_id)
        for retained in native_rows:
            source_row = int(retained['source_row'])
            require(1 <= source_row <= int(source['original_records']),
                    'Original source row is out of range')
            original = {field: retained[field] for field in source['columns']}
            origin = source_id, source_row
            require(origin in trace_by_origin, 'A selected source row has no provenance')
            require(origin not in checked, 'A selected source row is duplicated')
            checked.add(origin)
            trace = trace_by_origin[origin]
            serialized = (json.dumps(original, ensure_ascii=True, indent=2) + '\n').encode()
            require(digest(serialized) == trace['source_row_sha256'],
                    'Original source-row hash differs: ' + str(origin))
            expected_id = 'obs-' + digest((source_id + ':' + str(source_row)).encode())[:24]
            require(trace['observation_id'] == expected_id,
                    'Observation identity differs from original source identity')
            canonical_source_check(by_id[expected_id], original, source, trace)
    require(checked == set(trace_by_origin), 'Selected provenance lacks source rows')
    return len(checked)


def verify_summary(rows, excluded, summary):
    expected_keys = {(benchmark, solver) for benchmark in (*CASE_COUNTS, 'Total')
                     for solver in METHODS}
    require(len(summary) == 40 and {(r['benchmark'], r['solver']) for r in summary}
            == expected_keys, 'Expected forty benchmark/method summary rows')
    for group in summary:
        benchmark, solver = group['benchmark'], group['solver']
        chosen = [row for row in rows if row['solver'] == solver and
                  (benchmark == 'Total' or row['benchmark'] == benchmark)]
        na = [row for row in excluded if row['solver'] == solver and
              (benchmark == 'Total' or row['benchmark'] == benchmark)]
        counts = Counter(answer(row) for row in chosen if row['within_60s'] == 'true')
        instances = sum(CASE_COUNTS.values()) if benchmark == 'Total' else CASE_COUNTS[benchmark]
        expected = dict(instances=instances, observed=len(chosen), sat=counts['sat'],
                        unsat=counts['unsat'], solved=counts['sat'] + counts['unsat'],
                        unsolved_observed=len(chosen) - counts['sat'] - counts['unsat'],
                        not_applicable=len(na))
        require(len(chosen) + len(na) == instances, 'Benchmark/method coverage differs')
        for field, value in expected.items():
            require(int(group[field]) == value,
                    'Summary differs: ' + str((benchmark, solver, field)))


def verify_original_selectors(root, rows, traces, profiles, evidence):
    selectors_path = local_path(root, evidence['original_record_selectors_path'])
    members_path = local_path(root, evidence['original_members_index_path'])
    with gzip.open(selectors_path, 'rt', encoding='utf-8-sig', newline='') as stream:
        selectors = list(csv.DictReader(stream))
    with gzip.open(members_path, 'rt', encoding='utf-8-sig') as stream:
        members = json.load(stream)
    original = {row['observation_id']: row for row in rows if row['solver'] != 'LiMbS'}
    selected_ids = [row['observation_id'] for row in selectors]
    require(len(original) == len(selectors) == len(set(selected_ids)) == 19218,
            'Original evidence selector count or uniqueness differs')
    require(set(selected_ids) == set(original),
            'Original evidence selectors omit or introduce measured observations')
    old_evidence_ids = {profiles[row['measurement_id']]['evidence_id']
                        for row in original.values()}
    require(len(old_evidence_ids) == 4 and set(members) == old_evidence_ids,
            'Original member index archive identities differ')
    trace_by_id = {trace['observation_id']: trace for trace in traces}
    for evidence_id, entries in members.items():
        require(entries, 'Original archive has no indexed evidence members')
        for member, specification in entries.items():
            name = PurePosixPath(member)
            require(not name.is_absolute() and '..' not in name.parts,
                    'An original evidence member path is invalid')
            require(int(specification['bytes']) >= 0 and
                    len(specification['sha256']) == 64 and
                    all(c in '0123456789abcdef' for c in specification['sha256']),
                    'An original member byte/hash identity is invalid')
    used = set()
    for selector in selectors:
        row = original[selector['observation_id']]
        trace = trace_by_id[row['observation_id']]
        profile = profiles[row['measurement_id']]
        for field in ('measurement_id', 'benchmark', 'solver', 'case_id'):
            require(selector[field] == row[field],
                    'Original selector observation identity differs: ' + field)
        evidence_id = selector['evidence_id']
        require(evidence_id == trace['evidence']['evidence_id'] == profile['evidence_id'],
                'Original selector measurement/evidence relationship differs')
        member = selector['member']
        permitted = {trace['evidence'].get('record_member'),
                     trace['evidence'].get('raw_results_member'),
                     profile.get('raw_results_member')}
        require(member in permitted,
                'Original selector member differs from recorded provenance')
        require(member in members[evidence_id], 'A selected raw member is not indexed')
        require(selector['member_sha256'] == members[evidence_id][member]['sha256'],
                'Original selector/member hash identities differ')
        used.add((evidence_id, member))
        if selector['source_line']:
            require(int(selector['source_line']) >= 1 and
                    member.endswith('.jsonl') and
                    len(selector['raw_line_sha256']) == 64 and
                    all(c in '0123456789abcdef' for c in selector['raw_line_sha256']),
                    'Original JSONL record selector is invalid')
        else:
            require(member.endswith('.json') and not selector['raw_line_sha256'],
                    'Original JSON record selector is invalid')
    return dict(observations=len(selectors), selected_members=len(used),
                indexed_members=sum(len(entries) for entries in members.values()),
                archives=len(members))


def verify_limbs_evidence(root, rows, traces, profiles, evidence):
    chosen = {row['observation_id']: row for row in rows if row['solver'] == 'LiMbS'}
    require(len(chosen) == 2260, 'LiMbS evidence observation scope differs')
    trace_by_id = {trace['observation_id']: trace for trace in traces}
    evidence_ids = {profiles[row['measurement_id']]['evidence_id'] for row in chosen.values()}
    require(len(evidence_ids) == 1, 'LiMbS evidence archive identity differs')
    evidence_id = next(iter(evidence_ids))
    archive = next(entry for entry in evidence['archives'] if entry['evidence_id'] == evidence_id)
    with gzip.open(local_path(root, archive['members_index_path']), 'rt', encoding='utf-8') as stream:
        members = json.load(stream)
    with gzip.open(local_path(root, archive['source_map_path']), 'rt', encoding='utf-8') as stream:
        mapping = json.load(stream)
    require(mapping['selected_solvers'] == ['LiMbS'] and mapping['final_records'] == 2260
            and mapping['source_payload_bytes_modified'] is False,
            'LiMbS source archive selection scope differs')
    source_members = {item['member']: item for item in mapping['source_member_mapping']}
    require(len(source_members) == len(mapping['source_member_mapping']) and
            set(source_members) == set(members), 'LiMbS member/source maps differ')
    derived = mapping['derived_aggregate']['member']
    for member, item in source_members.items():
        require(item['sha256'] == members[member], 'LiMbS source member hash differs')
        if member != derived:
            require(item['payload_byte_identical'] is True and
                    item['sha256'] == item['source_member_sha256'] and
                    item['bytes'] == item['source_member_bytes'],
                    'LiMbS original member payload identity differs')
    reference_tables = {}
    final_members = {}
    run_plans = set()
    for oid, row in chosen.items():
        trace = trace_by_id[oid]
        record = trace['evidence']
        require(not set(record) & {'source_csv_member', 'raw_results_member', 'nested_archive_member'},
                'LiMbS evidence retains an obsolete container member reference')
        require(record['archive'] == archive['path'], 'LiMbS evidence archive path differs')
        member = record['final_record_member']
        require(member in members and members[member] == record['final_record_sha256'],
                'LiMbS final-record member/hash identity differs')
        require(PurePosixPath(member).name == 'final.json' and
                PurePosixPath(member).parent.parent.name == record['job_key'],
                'LiMbS final record and job identity differ')
        require(member not in final_members, 'A LiMbS final record is used twice')
        final_members[member] = row
        reference = trace['reference_status']
        require('archive_member' not in reference,
                'LiMbS reference status retains an obsolete archive member')
        path = reference['catalog_path']
        if path not in reference_tables:
            reference_tables[path] = {item['case_id']: item for item in read_csv(local_path(root, path))[1]}
        require(reference['value'] == row['expected_status'] ==
                reference_tables[path][row['case_id']]['expected_status'],
                'LiMbS reference label differs from the published input catalog')
        profile = profiles[row['measurement_id']]
        require(profile['evidence_archive'] == archive['path'] and
                profile['original_archive_sha256'] == mapping['source_archive_sha256'],
                'LiMbS measurement archive/source identity differs')
        plan = profile['run_plan_member']
        library = profile['source_root_member'] + 'solvers/baseline solvers/LiMbS.wl'
        require(plan in members and library in members and
                members[library] == profile['source_sha256'],
                'LiMbS measured run plan or solver source identity differs')
        run_plans.add(plan)
    required_finals = set(final_members)
    seen = set()
    checked_finals = set()
    with tarfile.open(local_path(root, archive['path']), 'r|gz') as retained:
        for entry in retained:
            require(entry.isfile() and entry.name not in seen,
                    'LiMbS archive has a non-file or duplicate member')
            require(entry.name in members and entry.size == source_members[entry.name]['bytes'],
                    'LiMbS archive member inventory or size differs')
            seen.add(entry.name)
            raw = retained.extractfile(entry).read()
            require(digest(raw) == members[entry.name], 'LiMbS archive member hash differs')
            if entry.name in required_finals:
                native = json.loads(raw)
                row = final_members[entry.name]
                for field in ('case_id', 'solver', 'benchmark', 'input_sha256', 'status'):
                    require(native[field] == row[field], 'LiMbS final-record identity differs: ' + field)
                checked_finals.add(entry.name)
            if entry.name in run_plans:
                plan = json.loads(raw)
                require(all(plan['fingerprint'] == profiles[row['measurement_id']]['measurement_fingerprint']
                            for row in chosen.values()), 'LiMbS recorded run-plan fingerprint differs')
    require(seen == set(members) and checked_finals == required_finals,
            'LiMbS retained member/final-record coverage differs')
    return dict(observations=len(chosen), final_records=len(checked_finals),
                payload_members=len(seen), obsolete_container_references=0)


def verify_table_cells(rows, selection):
    cells = selection['expected_table_cells']
    require(len(cells) == 168, 'Expected 168 paper cells for the ten methods')
    successes = [row for row in rows if row['within_60s'] == 'true']
    for cell in cells:
        method, benchmark = cell['method'], cell['benchmark']
        kind = cell['answer'].lower()
        require(kind in ('sat', 'unsat', 'all'), 'Unknown paper table answer')
        if method in ('Stage1', 'Stage2', 'Stage3'):
            stage = {'Stage1': 'Stage1', 'Stage2': 'Stage2', 'Stage3': 'OpenCAD'}[method]
            chosen = [r for r in successes if r['solver'] == 'HELMS' and r['stage'] == stage]
        else:
            require(method in METHODS, 'Unexpected solver in paper table cells')
            chosen = [r for r in successes if r['solver'] == method]
        count = sum((benchmark == 'Total' or r['benchmark'] == benchmark)
                    and (kind == 'all' or answer(r) == kind) for r in chosen)
        if cell['value'] is None:
            require(method in ('2D-LS', 'LS-WL') and kind == 'unsat' and count == 0,
                    'Unexpected dash in paper table')
        else:
            require(count == int(cell['value']), 'Paper cell differs: ' + str(cell))
    return len(cells)


def verify_claims(rows):
    success = defaultdict(dict)
    for row in rows:
        if row['within_60s'] == 'true':
            success[row['solver']][row['case_id']] = row
    def difference(other, kind, benchmark=None):
        return [row for case, row in success['HELMS'].items() if
                case not in success[other] and answer(row) == kind and
                (benchmark is None or row['benchmark'] == benchmark)]
    checks = (
        ('V1', 'sat', None, 3, 'Stage1'),
        ('V4', 'sat', 'RandInst', 85, 'Stage1'),
        ('V2', 'unsat', None, 3, 'Stage2'),
        ('V3', 'unsat', None, 7, 'OpenCAD'),
    )
    for other, kind, benchmark, count, stage in checks:
        chosen = difference(other, kind, benchmark)
        require(len(chosen) == count and all(row['stage'] == stage for row in chosen),
                'Observation 8 case/stage claim differs: ' + other)
    common = set(success['2D-LS']) & set(success['LS-WL'])
    require(len(common) == 1616, 'Observation 5 jointly solved count differs')
    slow = [case for case in common if max(Decimal(success[method][case]['solve_seconds'])
            for method in ('2D-LS', 'LS-WL')) > Decimal(1)]
    faster = sum(Decimal(success['2D-LS'][case]['solve_seconds']) <
                 Decimal(success['LS-WL'][case]['solve_seconds']) for case in slow)
    slower = sum(Decimal(success['2D-LS'][case]['solve_seconds']) >
                 Decimal(success['LS-WL'][case]['solve_seconds']) for case in slow)
    require((len(slow), faster, slower) == (107, 93, 14),
            'Observation 5 runtime comparison differs')
    extra = difference('LS-WL', 'sat', 'SMTLIB')
    require(len(extra) == 34 and Counter(row['stage'] for row in extra)
            == Counter(Stage1=33, Stage2=1), 'Observation 2 stage claim differs')
    return {'joint_sat': len(common), 'at_least_one_over_1s': len(slow),
            '2D_LS_faster': faster, 'LS_WL_faster': slower,
            'observation_8_case_and_stage_counts': [3, 85, 3, 7]}


def verify(root=None, skip_input_check=False):
    root = Path(root or Path(__file__).resolve().parents[1]).resolve()
    public_files = verify_manifest(root)
    selection = load_json(root / 'data/paper_selection.json')
    limit = Decimal(str(selection['reporting_limit_seconds']))
    require(limit == 60, 'Paper reporting limit differs')
    require(selection['case_counts'] == CASE_COUNTS, 'Paper benchmark sizes differ')
    require(len(selection['paper_sha256']) == 64, 'Missing pinned paper hash')
    solver_files = selection['public_solver_files']
    require(solver_files and 'solvers/paper solvers/HELMS.wl' in solver_files,
            'Missing public solver version identities')
    for relative, specification in solver_files.items():
        verify_file(root, relative, specification)
    selected_ids = set(selection['measurement_ids'])
    profiles = load_json(root / 'data/measurements.json')['profiles']
    require(len(selected_ids) == 39 and set(profiles) == selected_ids,
            'Selected measurement profile scope differs')
    index = load_json(root / 'data/index.json')
    rows = []
    for benchmark, expected_count in CASE_COUNTS.items():
        spec = index['benchmarks'][benchmark]
        fields, chosen = read_csv(root / 'data' / spec['results'])
        require(tuple(fields) == FIELDS, 'Canonical result fields differ')
        require(all(row['benchmark'] == benchmark for row in chosen),
                'Benchmark result grouping differs')
        require(len(chosen) == int(spec['observations']), 'Indexed observation count differs')
        require(len({row['case_id'] for row in chosen}) == expected_count,
                'Indexed distinct-input count differs')
        require(set(spec['solver_files']) == set(METHODS), 'Indexed solver set differs')
        for solver, relative in spec['solver_files'].items():
            other_fields, other_rows = read_csv(root / 'data' / relative)
            require(other_fields == fields and other_rows == [
                row for row in chosen if row['solver'] == solver],
                'Solver view differs: ' + relative)
        rows.extend(chosen)
    excluded_fields, excluded = read_csv(root / 'data/applicability.csv')
    require(tuple(excluded_fields) == FIELDS, 'Applicability fields differ')
    require(len(rows) == 21478 and len(excluded) == 1122,
            'Selected observation/applicability counts differ')
    require(all(row['status'] == 'not_applicable' for row in excluded),
            'Applicability contains measured outcomes')
    require(all(row['status'] != 'not_applicable' for row in rows),
            'Measured results contain applicability rows')
    combined = rows + excluded
    require(len({(r['solver'], r['case_id']) for r in combined}) == 22600,
            'Duplicate or missing solver/input pair')
    require(len({r['observation_id'] for r in combined}) == 22600,
            'Duplicate observation identity')
    require({r['measurement_id'] for r in combined} == selected_ids,
            'Result and measurement scope differ')
    for row in combined:
        profile = profiles[row['measurement_id']]
        require(profile['solver'] == row['solver'] and profile['benchmark'] == row['benchmark'],
                'Measurement method/benchmark differs')
        expected = str(within_limit(row, limit)).lower()
        require(row['within_60s'] == expected, '60-second reporting flag differs')
    traces = [json.loads(line) for line in (root / 'data/provenance.jsonl').read_text(
        encoding='utf-8-sig').splitlines() if line.strip()]
    require(len(traces) == 22600, 'Provenance count differs')
    sources = load_json(root / 'data/sources.json')['sources']
    require(len(sources) == 7, 'Selected original source count differs')
    source_rows = verify_sources(root, combined, traces, sources)
    evidence = load_json(root / 'data/evidence/index.json')
    archives = evidence['archives']
    evidence_ids = {entry['evidence_id'] for entry in archives}
    require(len(evidence_ids) == len(archives), 'Duplicate evidence archive identity')
    for entry in archives:
        verify_file(root, entry['path'], entry)
    require(all(trace['evidence']['evidence_id'] in evidence_ids for trace in traces),
            'Provenance refers to missing evidence archive')
    for row in combined:
        profile = profiles[row['measurement_id']]
        require(profile['evidence_id'] in evidence_ids,
                'Measurement refers to missing evidence archive')
    by_id = {row['observation_id']: row for row in combined}
    for trace in traces:
        row = by_id[trace['observation_id']]
        require(trace['applicability_only'] == (row['status'] == 'not_applicable'),
                'Provenance applicability differs from the retained source')
        require(trace['evidence']['evidence_id'] ==
                profiles[row['measurement_id']]['evidence_id'],
                'Observation and measurement evidence archives differ')
        for key, value in trace['evidence'].get('selector', {}).items():
            if key in ('case_id', 'solver', 'input_sha256'):
                require(row[key] == value, 'Evidence selector differs from observation')
    original_selectors = verify_original_selectors(root, rows, traces, profiles, evidence)
    limbs_evidence = verify_limbs_evidence(root, rows, traces, profiles, evidence)
    _, summary = read_csv(root / 'data/summary.csv')
    verify_summary(rows, excluded, summary)
    paper_cells = verify_table_cells(rows, selection)
    claims = verify_claims(rows)
    _, instances = read_csv(root / 'data/instances.csv')
    _, representations = read_csv(root / 'data/input_representations.csv')
    require(len(instances) == 2260 and len(representations) == 2349,
            'Input metadata scope differs')
    input_variants = {(r['benchmark'], r['case_id'], r['input_sha256']) for r in representations}
    require(all((r['benchmark'], r['case_id'], r['input_sha256']) in input_variants
                for r in combined), 'Observation input absent from input representations')
    for benchmark, spec in index['benchmarks'].items():
        require(read_csv(root / 'data' / spec['instances'])[1] == [r for r in instances
                if r['benchmark'] == benchmark], 'Benchmark instance view differs')
        require(read_csv(root / 'data' / spec['input_representations'])[1] == [
                r for r in representations if r['benchmark'] == benchmark],
                'Benchmark input representation view differs')
    input_check = None
    if not skip_input_check:
        module_spec = importlib.util.spec_from_file_location(
            '_selected_inputs_check', root / 'data/check_input_equivalence.py')
        module = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(module)
        input_check = module.verify(root)
        require(input_check['passed'], 'Exact input equivalence check failed')
    return dict(passed=True, public_files=public_files, methods=len(METHODS),
                measurement_profiles=len(profiles), actual_observations=len(rows),
                not_applicable=len(excluded), original_source_rows=source_rows,
                evidence_archives=len(archives), summary_rows=len(summary),
                original_evidence_selectors=original_selectors,
                limbs_evidence=limbs_evidence,
                pinned_solver_files=len(solver_files),
                checked_paper_cells=paper_cells, claims=claims,
                input_equivalence=input_check)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path)
    parser.add_argument('--skip-input-check', action='store_true')
    args = parser.parse_args()
    sys.dont_write_bytecode = True
    print(json.dumps(verify(args.root, args.skip_input_check), indent=2))


if __name__ == '__main__':
    main()
