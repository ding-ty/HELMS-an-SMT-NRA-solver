#!/usr/bin/env python3
"""Run the benchmark suite with the supplied solver configurations and resource profiles."""
from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import sys
import uuid
import zipfile

from protocols import core, baseline, opencad


ROOT = Path(__file__).resolve().parents[1]
SOLVERS = ('HELMS', '2D-LS', 'V1', 'V2', 'V3', 'V4', 'V5', 'LS-WL', 'LiMbS', 'OpenCAD')
DEFAULT_SOLVERS = SOLVERS
BENCHMARKS = ('SMTLIB', 'RandInst', 'SpecInst')
SAT_ONLY = {'2D-LS', 'LS-WL'}
DEFAULT_TIMEOUT = 60.0
DEFAULT_SEED = 314159
DEFAULT_MANIFEST = ROOT / 'benchmarks/experiment_default.jsonl'
DEFAULT_INPUTS = ROOT / 'benchmarks/default_inputs.zip'
LIBRARY_SHA256 = '450699e092757f2f4d61b2ad9b7205e8ed5fc054be1ebf4c62bfe614bf363bde'
LIBRARY_UPSTREAM_COMMIT = '7e1457b528c848343c6997bafb019ed4b39af413'


def sha(path):
    return core.sha256_file(Path(path))


def input_member(case):
    path = PurePosixPath(case['input_path'])
    if (path.is_absolute() or '..' in path.parts or path.parts[:2] != ('benchmarks', 'inputs')
            or len(path.parts) < 3 or path.as_posix() != case['input_path']):
        raise ValueError('Invalid benchmark input path: ' + str(case['case_id']))
    return PurePosixPath(*path.parts[2:]).as_posix()


def cases_for(args):
    cases, seen = [], set()
    for line in DEFAULT_MANIFEST.read_text(encoding='utf-8-sig').splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        case_id = row['case_id']
        if not isinstance(case_id, str) or case_id in seen:
            raise ValueError('Duplicate or invalid benchmark case ID')
        seen.add(case_id)
        group = row.get('benchmark_group', row.get('benchmark'))
        if group not in args.benchmark or (args.case_id and case_id not in args.case_id):
            continue
        if row.get('expected_status') not in {'sat', 'unsat', 'unknown'}:
            raise ValueError('Invalid reference status in benchmark manifest')
        input_member(row)
        cases.append({**row, 'benchmark_group': group})
    if args.case_id and set(args.case_id) - {case['case_id'] for case in cases}:
        raise ValueError('A requested case ID was not found in the selected benchmarks')
    if not cases:
        raise ValueError('No benchmark cases selected')
    with zipfile.ZipFile(DEFAULT_INPUTS) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError('Duplicate members in the benchmark input archive')
        for case in cases:
            if hashlib.sha256(archive.read(input_member(case))).hexdigest() != case['input_sha256']:
                raise ValueError('Input archive SHA-256 mismatch: ' + case['case_id'])
    return cases


def unpack_inputs(cases):
    """Extract verified inputs without overwriting an existing input file."""
    with zipfile.ZipFile(DEFAULT_INPUTS) as archive:
        for case in cases:
            destination = ROOT / case['input_path']
            if destination.exists():
                if not destination.is_file() or sha(destination) != case['input_sha256']:
                    raise ValueError('Existing extracted input differs from the manifest: ' + str(destination))
                continue
            raw = archive.read(input_member(case))
            if hashlib.sha256(raw).hexdigest() != case['input_sha256']:
                raise ValueError('Input archive changed during extraction')
            destination.parent.mkdir(parents=True, exist_ok=True)
            with destination.open('xb') as stream:
                stream.write(raw)


def profile_for(solver, benchmark):
    if solver == 'OpenCAD':
        return 'independent-OpenCAD-v1'
    if solver == 'LiMbS':
        return 'standalone-baseline'
    if solver in {'HELMS', 'LS-WL'}:
        return 'windows-safe8g-serial-v1'
    if benchmark == 'SMTLIB' and solver != '2D-LS':
        return 'adaptive-windows-job-v3'
    return 'windows-safe8g-serial-v1'


def selected_sections(args, cases):
    sections = []
    for solver in args.solvers:
        for group in args.benchmark:
            selected = [case for case in cases if case['benchmark_group'] == group
                        and (solver not in SAT_ONLY or case['expected_status'] != 'unsat')]
            if selected:
                sections.append({'solver': solver, 'benchmark': group, 'cases': selected,
                                 'profile': profile_for(solver, group),
                                 'configuration': ('config/opencad_config.json' if solver == 'OpenCAD'
                                                   else 'config/2dls_config.json' if solver == '2D-LS'
                                                   else 'config/helms_config.json' if solver == 'HELMS'
                                                   else 'config/lswl_config.json' if solver == 'LS-WL'
                                                   else 'config/run_config.json')})
    return sections


def scientific_source_hashes():
    paths = [ROOT / 'runner/run_experiments.py', ROOT / 'runner/prepare_default_inputs.py',
             DEFAULT_MANIFEST, DEFAULT_INPUTS, ROOT / 'benchmarks/default_input_map.json',
             ROOT / 'benchmarks/experiment_all.jsonl',
             ROOT / 'benchmarks/inputs.zip', *sorted((ROOT / 'runner/protocols').glob('*.py')),
             *sorted((ROOT / 'components').rglob('*.wl')), *sorted((ROOT / 'components').rglob('*.wls')),
             *sorted((ROOT / 'solvers').rglob('*.wl')), *sorted((ROOT / 'config').glob('*.json'))]
    return {path.relative_to(ROOT).as_posix(): sha(path) for path in paths}


def framework_section(section, manifest, output, executable, timeout_seconds, seed):
    if section['profile'] == 'adaptive-windows-job-v3':
        from protocols import adaptive as controller
    else:
        from protocols import safe as controller
    argv = ['run', '--manifest', str(manifest), '--config', str(ROOT / section['configuration']),
            '--solvers', section['solver'], '--shards', '1', '--shard-index', '0',
            '--output-dir', str(output), '--wolfram-command', executable,
            '--timeout', str(timeout_seconds), '--startup-grace', '60', '--seed', str(seed),
            '--case-policy', 'all']
    return controller.main(argv)


def opencad_configuration(section):
    """Read effective CLI settings and reject unsupported fixed-protocol changes."""
    configuration = json.loads((ROOT / section['configuration']).read_bytes(),
                               parse_constant=opencad.reject_nonfinite)
    fixed = {'protocol': 'independent_OpenCAD_v1',
             'watchdog_grace_seconds': 5.0, 'finalization_grace_seconds': 60.0,
             'verification_budget_seconds': 30.0,
             'host_guard': 'available_system_commit;physical_low_is_warning_only',
             'max_extra_precision': 'Infinity',
             'input_policy': 'original_exact_CNF_and_manifest_variable_order;no_LS_or_MCSAT_preprocessing;no_reference_answer_in_request',
             'decision_policy': 'GenericCylindricalDecomposition;FindInstance_only_on_returned_cell;exact_SAT_validation',
             'timing_basis': 'full_1200_or_declared_budget_per_attempt;startup_and_verification_separate;cell_witness_extraction_included',
             'selection_policy': 'all_final_outcomes_retained;only_unfinalized_attempts_may_be_recovered;no_best_of_retries'}
    for key, expected in fixed.items():
        if configuration.get(key) != expected:
            raise ValueError('OpenCAD configuration changes a fixed measured-protocol setting: ' + key)
    for key in ('seed', 'cpu_index', 'job_private_commit_limit_bytes'):
        value = configuration.get(key)
        if type(value) is not int or (key != 'seed' and value < (1 if key == 'job_private_commit_limit_bytes' else 0)):
            raise ValueError('Invalid OpenCAD integer setting: ' + key)
    for key in ('timeout_seconds', 'startup_grace_seconds', 'reserve_commit_mb'):
        value = configuration.get(key)
        if type(value) not in (int, float) or not 0 < value < float('inf'):
            raise ValueError('Invalid OpenCAD positive finite setting: ' + key)
    return configuration


def opencad_section(section, output, executable, timeout_seconds, seed):
    """Run the recovered independent OpenCAD protocol with its configured limits."""
    configuration = opencad_configuration(section)
    argv = ['run', '--benchmark', section['benchmark'], '--output-dir', str(output),
            '--wolfram-command', executable,
            '--timeout', str(timeout_seconds),
            '--memory-gib', str(configuration['job_private_commit_limit_bytes'] / 1024**3),
            '--reserve-mb', str(configuration['reserve_commit_mb']),
            '--startup-grace', str(configuration['startup_grace_seconds']),
            '--seed', str(seed), '--cpu', str(configuration['cpu_index'])]
    for case in section['cases']:
        argv.extend(['--case-id', case['case_id']])
    return opencad.run(opencad.parser().parse_args(argv))


def baseline_section(section, manifest, output, executable, timeout_seconds, seed):
    """Use the measured independent-worker supervision without changing its limits."""
    library = ROOT / 'solvers/baseline solvers/LiMbS.wl'
    if sha(library) != LIBRARY_SHA256:
        raise ValueError('The supplied LiMbS library differs from its pinned identity')
    output.mkdir(parents=True, exist_ok=False)
    lock = output / '.runner.lock'
    baseline.write_new_json(lock, {'pid': os.getpid(), 'session': baseline.SESSION})
    rows = baseline.load_manifest(manifest)
    runtime = baseline.probe_runtime(executable)
    source_identity_verified = section['solver'] != 'LiMbS'
    reference_version_unresolved = section['solver'] == 'LiMbS' and section['benchmark'] == 'SMTLIB'
    plan = {'schema_version': 1, 'protocol': 'standalone_baselines_artifact_v1',
            'solvers': [section['solver']], 'benchmarks': [section['benchmark']], 'cases': rows,
            'input_manifest_sha256': sha(manifest), 'sources': scientific_source_hashes(),
            'runtime': runtime, 'kernel': executable,
            'worker_script': str(ROOT / 'components/BaselineWorker.wls'),
            'seed': seed, 'timeout_seconds': timeout_seconds, 'startup_grace_seconds': 60.0,
            'finalization_grace_seconds': 60, 'watchdog_grace_seconds': 10,
            'cpu_index': 0, 'reserve_mb': 1024.0,
            'host_guard_policy': 'windows_available_commit;other_min_available_memory',
            'timing_basis': 'full_solve_budget_per_attempt;startup_excluded;final_attempt_no_prior_time_charge',
            'selection_policy': 'one_final_record_per_job;completed_outcomes_never_automatically_retried',
            'host': {'system': platform.system(), 'release': platform.release(),
                     'machine': platform.machine(), 'logical_cpus': os.cpu_count()},
            'library_revision': {'active_source': library.relative_to(ROOT).as_posix(),
                                 'active_source_sha256': LIBRARY_SHA256,
                                 'upstream_repository': 'https://github.com/lihaokun/LiMbS',
                                 'upstream_commit': LIBRARY_UPSTREAM_COMMIT},
            'source_identity_verified': source_identity_verified,
            'reference_measurement_version_unresolved': reference_version_unresolved,
            'reference_measurement_implementation_matches': source_identity_verified,
            'reference_source_relation': ('library_version_not_identified_in_retained_csv'
                if reference_version_unresolved else 'supplied_upstream_library_differs_from_recorded_library'
                if section['solver'] == 'LiMbS' else 'independent_baseline_worker'),
            'jobs': [{'job_key': baseline.sha(baseline.canonical({'solver': section['solver'],
                                  'case_id': case['case_id'], 'input_sha256': case['input_sha256']})),
                      'case_id': case['case_id'], 'solver': section['solver']} for case in rows]}
    plan['fingerprint'] = baseline.sha(baseline.canonical(plan))
    baseline.write_new_json(output / 'run_plan.json', plan)
    by_id = {case['case_id']: case for case in rows}
    try:
        for number, job in enumerate(plan['jobs'], 1):
            print(f'START [{number}/{len(rows)}] {job["case_id"]} {section["solver"]}', flush=True)
            record = baseline.execute_job(plan, by_id[job['case_id']], job, output)
            if record is None:
                print('Attempt interrupted; evidence preserved without inferring a solver outcome.', flush=True)
                return 75
            print(f'DONE {job["case_id"]} {section["solver"]}: {record["effective_status"]}', flush=True)
            if record['effective_status'] in {'invalid_model', 'conflict'}:
                return 1
        return 0
    finally:
        lock.unlink(missing_ok=True)


def write_summary(output, sections):
    rows = []
    for section in sections:
        path = output / section['benchmark'] / section['solver'] / 'results.jsonl'
        records = baseline.read_journal(path)
        counts = Counter(record.get('effective_status', 'error') for record in records)
        rows.append({'benchmark': section['benchmark'], 'solver': section['solver'],
                     'profile': section['profile'], 'planned': len(section['cases']),
                     'final_records': len(records), 'solved': counts['sat'] + counts['unsat'],
                     **{status: counts[status] for status in ('sat', 'unsat', 'unknown', 'timeout', 'memout', 'error',
                                                            'invalid', 'invalid_model', 'conflict')},
                     'pending': len(section['cases']) - len(records)})
    temporary = output / 'summary.csv.tmp'
    with temporary.open('w', encoding='utf-8', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    temporary.replace(output / 'summary.csv')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wolfram-command', help='Path to the activated Mathematica 14.0 console kernel')
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'results', help='New or empty output directory')
    parser.add_argument('--solvers', nargs='+', choices=SOLVERS, default=list(DEFAULT_SOLVERS))
    parser.add_argument('--benchmark', nargs='+', choices=BENCHMARKS, default=list(BENCHMARKS))
    parser.add_argument('--case-id', nargs='+', help='Optional exact case IDs for a small check')
    parser.add_argument('--dry-run', action='store_true', help='Check inputs and print the plan without starting kernels')
    parser.add_argument('--timeout', type=float, default=DEFAULT_TIMEOUT, help='Solve budget per attempt in seconds (default: 60)')
    parser.add_argument('--seed', type=int, default=DEFAULT_SEED, help='Random seed set automatically in each fresh kernel (default: 314159)')
    args = parser.parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('--timeout must be finite and positive')
    if len(args.solvers) != len(set(args.solvers)) or len(args.benchmark) != len(set(args.benchmark)):
        parser.error('Solver and benchmark selections must not contain duplicates')
    cases = cases_for(args)
    sections = selected_sections(args, cases)
    for section in sections:
        if section['solver'] == 'OpenCAD':
            opencad_configuration(section)
    if not sections:
        raise ValueError('No applicable solver/instance combinations selected')
    overview = [{'solver': s['solver'], 'benchmark': s['benchmark'], 'jobs': len(s['cases']),
                 'profile': s['profile'], 'configuration': s['configuration']} for s in sections]
    print(json.dumps({'planned_jobs': sum(row['jobs'] for row in overview), 'sections': overview,
                      'selected_inputs': len(cases), 'seed': args.seed,
                      'solve_timeout_seconds_per_attempt': args.timeout}, indent=2), flush=True)
    if args.dry_run:
        return 0
    if os.name != 'nt':
        raise ValueError('The recorded resource profiles require native 64-bit Windows Python')
    if not args.wolfram_command:
        parser.error('--wolfram-command is required unless --dry-run is used')
    executable = str(Path(shutil.which(args.wolfram_command) or args.wolfram_command).resolve())
    if not Path(executable).is_file():
        raise ValueError('Mathematica kernel executable not found')
    output = args.output_dir.resolve()
    data = (ROOT / 'data').resolve()
    if output == ROOT.resolve() or output == data or data in output.parents:
        raise ValueError('Choose a separate measurement output directory')
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError('Output directory is not empty; choose a new directory to preserve existing evidence')
    lock = output / '.runner.lock'
    baseline.write_new_json(lock, {'pid': os.getpid(), 'session': uuid.uuid4().hex})
    try:
        unpack_inputs(cases)
        if 'OpenCAD' in args.solvers:
            # The measured OpenCAD controller validates the complete canonical manifest.
            # Extract all inputs before its filtered section without changing any input bytes.
            unpack_inputs(opencad.journal(DEFAULT_MANIFEST))
        plan = {'schema_version': 1, 'sections': overview, 'seed': args.seed,
                'solve_timeout_seconds_per_attempt': args.timeout, 'source_sha256': scientific_source_hashes(),
                'events': 'opaque_session_relative_elapsed', 'created': core.event_stamp()}
        plan['fingerprint'] = core.digest_object(plan)
        core.write_json(output / 'run_plan.json', plan)
        write_summary(output, sections)
        for section in sections:
            directory = output / section['benchmark'] / section['solver']
            manifest = output / 'manifests' / section['benchmark'] / (section['solver'] + '.jsonl')
            manifest.parent.mkdir(parents=True, exist_ok=True)
            with manifest.open('x', encoding='utf-8', newline='\n') as stream:
                for case in section['cases']:
                    stream.write(json.dumps(case, sort_keys=True, ensure_ascii=True) + '\n')
            print(f'SERIES {section["benchmark"]} {section["solver"]}: {section["profile"]}', flush=True)
            code = (opencad_section(section, directory, executable, args.timeout, args.seed)
                    if section['profile'] == 'independent-OpenCAD-v1' else
                    baseline_section(section, manifest, directory, executable, args.timeout, args.seed)
                    if section['profile'] == 'standalone-baseline' else
                    framework_section(section, manifest, directory, executable, args.timeout, args.seed))
            write_summary(output, sections)
            records = baseline.read_journal(directory / 'results.jsonl')
            if code != 0 and len(records) != len(section['cases']):
                print('Series stopped with incomplete observations; inspect the preserved evidence.', flush=True)
                return code
            if any(record.get('effective_status') in {'conflict', 'invalid', 'invalid_model'} for record in records):
                return 1
        print('Measurements finished. See ' + str(output / 'summary.csv'), flush=True)
        return 0
    finally:
        lock.unlink(missing_ok=True)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print('Interrupted. Existing observations and attempt evidence are preserved.', file=sys.stderr)
        raise SystemExit(130)
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        print('ERROR: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
