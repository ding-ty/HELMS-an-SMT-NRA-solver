"""Independent, serial OpenCAD measurements; original attempts are preserved."""
from __future__ import annotations
import argparse
from collections import Counter
import csv
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
import time
import uuid

from .opencad_process import WorkerProcess, memory_available_mb, process_identity, same_process_alive

ROOT = Path(__file__).resolve().parents[2]
SESSION = uuid.uuid4().hex
ORIGIN = time.perf_counter()
GROUPS = ('SMTLIB', 'RandInst', 'SpecInst')


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def stamp():
    return {'session': SESSION, 'elapsed_seconds': time.perf_counter() - ORIGIN}


def reject_nonfinite(value):
    raise ValueError('Nonfinite JSON number: ' + value)


def read_json(path):
    return json.loads(Path(path).read_bytes(), parse_constant=reject_nonfinite)


def write_new(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(canonical(value) + b'\n')
        stream.flush()
        os.fsync(stream.fileno())


def append(path, value):
    with Path(path).open('ab') as stream:
        stream.write(canonical(value) + b'\n')
        stream.flush()
        os.fsync(stream.fileno())


def derived(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    temporary.write_bytes(canonical(value) + b'\n')
    os.replace(temporary, path)


def journal(path):
    path = Path(path)
    if not path.exists():
        return []
    raw = path.read_bytes()
    if raw and not raw.endswith(b'\n'):
        raise ValueError('Incomplete journal tail: preserve it and use --resume --recover-interrupted')
    values = [json.loads(line, parse_constant=reject_nonfinite) for line in raw.splitlines()]
    if not all(isinstance(x, dict) for x in values):
        raise ValueError('Journal contains a non-object row')
    return values


def recover_tail(output):
    path = output / 'results.jsonl'
    if not path.exists():
        return
    raw = path.read_bytes()
    good = []
    for index, line in enumerate(raw.splitlines(keepends=True)):
        try:
            value = json.loads(line, parse_constant=reject_nonfinite)
            if not isinstance(value, dict):
                raise ValueError('Non-object row')
        except (ValueError, UnicodeError):
            if index != len(raw.splitlines(keepends=True)) - 1:
                raise ValueError('Corrupt interior journal row; automatic recovery refused')
            break
        good.append(line if line.endswith(b'\n') else line + b'\n')
    rebuilt = b''.join(good)
    if rebuilt != raw:
        preserved = output / 'recovery' / ('original_results_' + uuid.uuid4().hex + '.jsonl')
        preserved.parent.mkdir(exist_ok=True)
        path.rename(preserved)
        with path.open('xb') as stream:
            stream.write(rebuilt)
            stream.flush()
            os.fsync(stream.fileno())
        event(output, 'journal_tail_recovered', original=preserved.relative_to(output).as_posix(), original_sha256=sha(raw))


def event(output, name, **extra):
    append(output / 'events.jsonl', {'event': name, 'stamp': stamp(), **extra})


def load_cases():
    manifest = ROOT / 'benchmarks/experiment_default.jsonl'
    rows = journal(manifest)
    seen = set()
    for row in rows:
        if row['case_id'] in seen or row['benchmark_group'] not in GROUPS or row['expected_status'] not in {'sat', 'unsat', 'unknown'}:
            raise ValueError('Invalid benchmark manifest')
        seen.add(row['case_id'])
        path = (ROOT / row['input_path']).resolve()
        if not path.is_relative_to((ROOT / 'benchmarks/inputs').resolve()):
            raise ValueError('Input path escapes canonical input directory')
        if sha(path.read_bytes()) != row['input_sha256']:
            raise ValueError('Input hash mismatch: ' + row['case_id'])
    return rows


def kernel_path(value):
    name = value or os.environ.get('WOLFRAM_COMMAND') or shutil.which('math') or shutil.which('WolframKernel')
    if not name:
        raise ValueError('Supply --wolfram-command with the activated Mathematica console kernel')
    path = Path(shutil.which(name) or name).resolve()
    if not path.is_file():
        raise ValueError('Kernel executable does not exist: ' + str(path))
    return str(path)


def probe_runtime(kernel):
    with tempfile.TemporaryDirectory(prefix='opencad_probe_') as directory:
        directory = Path(directory)
        script = directory / 'probe.wls'
        script.write_text('Print["OPENCAD_RUNTIME_BEGIN"];Print[ExportString['
                          '<|"wolfram_version"->$Version,"system_id"->$SystemID,"OpenCAD_available"->'
                          '(Length[Names["System`GenericCylindricalDecomposition"]]>0)|>,"RawJSON"]];'
                          'Print["OPENCAD_RUNTIME_END"];Exit[0];', encoding='ascii')
        with (directory / 'stdout.log').open('wb') as stdout, (directory / 'stderr.log').open('wb') as stderr:
            worker = WorkerProcess([kernel, '-noinit', '-script', str(script)], stdout, stderr, ROOT)
            launched = time.perf_counter()
            try:
                while worker.poll() is None and time.perf_counter() - launched < 120:
                    time.sleep(.1)
                code = worker.poll()
            finally:
                worker.close()
        logs = ((directory / 'stdout.log').read_bytes() + (directory / 'stderr.log').read_bytes()).decode('utf-8', errors='replace')
        match = re.search(r'OPENCAD_RUNTIME_BEGIN\s*(.*?)\s*OPENCAD_RUNTIME_END', logs, re.S)
        if code != 0 or not match:
            raise ValueError(f'Mathematica startup/license probe failed (exit {code}); check executable/activation. ' + logs[-1800:])
        value = json.loads(match[1])
        if not value['wolfram_version'].startswith('14.0') or value['system_id'] != 'Windows-x86-64' or not value['OpenCAD_available']:
            raise ValueError('This controlled comparison requires Mathematica 14.0 with GenericCylindricalDecomposition')
        return {k: value[k] for k in ('wolfram_version', 'system_id')}


def make_plan(args):
    groups = list(GROUPS) if args.benchmark == 'All' else [args.benchmark]
    cases = [r for r in load_cases() if r['benchmark_group'] in groups and (not args.case_id or r['case_id'] in args.case_id)]
    if args.case_id and set(args.case_id) != {c['case_id'] for c in cases}:
        raise ValueError('Requested case is not in the selected benchmark')
    cases.sort(key=lambda c: (GROUPS.index(c['benchmark_group']), c['case_id']))
    if args.max_cases is not None:
        if args.max_cases < 1:
            raise ValueError('--max-cases must be positive')
        cases = cases[:args.max_cases]
    if not cases:
        raise ValueError('No cases selected')
    if not all(math.isfinite(v) and v > 0 for v in (args.timeout, args.memory_gib, args.startup_grace, args.reserve_mb)):
        raise ValueError('Invalid time or memory settings')
    source_files = [Path(__file__).resolve(), ROOT / 'runner/protocols/opencad_process.py', ROOT / 'components/OpenCADWorker.wls']
    kernel = kernel_path(args.wolfram_command)
    plan = {
        'schema_version': 1, 'protocol': 'independent_OpenCAD_v1', 'solver': 'OpenCAD',
        'benchmarks': groups, 'cases': cases, 'seed': args.seed, 'timeout_seconds': args.timeout,
        'startup_grace_seconds': args.startup_grace, 'watchdog_grace_seconds': 5.0,
        'finalization_grace_seconds': 60.0, 'verification_budget_seconds': 30.0,
        'job_private_commit_limit_bytes': int(args.memory_gib * 1024**3), 'reserve_commit_mb': args.reserve_mb,
        'host_guard': 'available_system_commit;physical_low_is_warning_only', 'cpu_index': args.cpu,
        'kernel': kernel, 'runtime_identity': probe_runtime(kernel),
        'kernel_executable_sha256': sha(Path(kernel).read_bytes()),
        'manifest_sha256': sha((ROOT / 'benchmarks/experiment_all.jsonl').read_bytes()),
        'sources': {p.relative_to(ROOT).as_posix(): sha(p.read_bytes()) for p in source_files},
        'timing_basis': 'full_1200_or_declared_budget_per_attempt;startup_and_verification_separate;cell_witness_extraction_included',
        'input_policy': 'original_exact_CNF_and_manifest_variable_order;no_LS_or_MCSAT_preprocessing;no_reference_answer_in_request',
        'decision_policy': 'GenericCylindricalDecomposition;FindInstance_only_on_returned_cell;exact_SAT_validation',
        'selection_policy': 'all_final_outcomes_retained;only_unfinalized_attempts_may_be_recovered;no_best_of_retries',
        'max_extra_precision': 'Infinity',
    }
    plan['fingerprint'] = sha(canonical(plan))
    return plan


def checked_plan(output):
    plan = read_json(output / 'run_plan.json')
    payload = dict(plan)
    fingerprint = payload.pop('fingerprint')
    if sha(canonical(payload)) != fingerprint:
        raise ValueError('Saved plan fingerprint mismatch')
    return plan


def job_key(plan, case):
    return sha(canonical({'fingerprint': plan['fingerprint'], 'case_id': case['case_id']}))


def exact(node, model):
    op = node['op']
    if op == 'int': return Fraction(int(node['value']))
    if op == 'rat': return Fraction(int(node['numerator']), int(node['denominator']))
    if op == 'var': return model[node['name']]
    if op == 'add': return sum((exact(n, model) for n in node['args']), Fraction())
    if op == 'mul':
        value = Fraction(1)
        for child in node['args']: value *= exact(child, model)
        return value
    if op == 'pow': return exact(node['base'], model) ** node['exponent']
    raise ValueError('Unsupported exact AST')


def validate_worker(worker, case, plan, request_id, exit_code):
    status = worker.get('actual_status')
    if status not in {'sat', 'unsat', 'timeout', 'unknown', 'error'}:
        raise ValueError('Invalid worker status')
    seconds = worker.get('solve_seconds')
    if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds < 0:
        raise ValueError('Invalid solve time')
    validation = {'unsat_independently_reproved': False}
    effective = status
    if status in {'sat', 'unsat'}:
        identities = {'case_id': case['case_id'], 'solver': 'OpenCAD', 'request_id': request_id,
                      'input_sha256': case['input_sha256'], 'runtime_identity': plan['runtime_identity']}
        if any(worker.get(k) != v for k, v in identities.items()) or exit_code != 0:
            validation['protocol_error'] = 'worker_identity_or_exit_mismatch'
            effective = 'error'
        elif seconds > plan['timeout_seconds']:
            validation['solve_budget_exceeded_after_return'] = True
            effective = 'timeout'
        if status == 'sat':
            data = read_json(ROOT / case['input_path'])
            values = worker.get('model_values')
            valid = False
            if isinstance(values, dict) and set(values) == set(data['variables']):
                if all(isinstance(v, str) and re.fullmatch(r'[+-]?\d+(?:/\d+)?', v) for v in values.values()):
                    model = {k: Fraction(v) for k, v in values.items()}
                    polys = [exact(p, model) for p in data['polynomials']]
                    valid = all(any(sign * polys[index-1] > 0 for index, sign in clause) for clause in data['clauses'])
                    validation['model'] = 'independent_exact_rational_pass' if valid else 'independent_exact_rational_fail'
                else:
                    native = worker.get('model_validation', {})
                    valid = native.get('valid') is True and native.get('exact') is True
                    validation['model'] = 'wolfram_exact_algebraic_pass' if valid else 'algebraic_validation_missing'
            if not valid:
                effective = 'invalid_model'
        if case['expected_status'] in {'sat', 'unsat'}:
            matches = status == case['expected_status']
            validation['reference_comparison'] = 'matches' if matches else 'conflict'
            if not matches:
                effective = 'conflict'
        else:
            validation['reference_comparison'] = 'reference_unknown'
    return effective, validation


def validate_records(output, plan):
    records = journal(output / 'results.jsonl')
    cases = {c['case_id']: c for c in plan['cases']}
    seen = set()
    for row in records:
        case = cases.get(row.get('case_id'))
        if case is None or row.get('fingerprint') != plan['fingerprint'] or row['job_key'] != job_key(plan, case) or row['job_key'] in seen:
            raise ValueError('Duplicate, unplanned or mismatched final record')
        seen.add(row['job_key'])
        for field, value in [('solver', 'OpenCAD'), ('input_sha256', case['input_sha256']), ('expected_status', case['expected_status'])]:
            if row.get(field) != value:
                raise ValueError('Final record identity mismatch: ' + field)
        if row.get('termination_trigger', {}).get('kind') == 'declared_job_memory_limit':
            effective = 'memout'
            if not row['resource_usage']['memory_limit_events']:
                raise ValueError('MEMOUT lacks declared-limit event evidence')
        else:
            effective, _ = validate_worker(row['worker_result'], case, plan, row['request_id'], row['worker_exit_code'])
        if row['effective_status'] != effective or row['count_as_solved'] != (effective in {'sat', 'unsat'}):
            raise ValueError('Final outcome disagrees with evidence')
        if row.get('solve_seconds') != row['worker_result'].get('solve_seconds') or row.get('actual_status') != row['worker_result'].get('actual_status'):
            raise ValueError('Final answer/time disagrees with the preserved worker observation')
        attempt = (output / row['attempt_directory']).resolve()
        if not attempt.is_relative_to(output.resolve()):
            raise ValueError('Evidence path escapes output')
        if row.get('worker_result_sha256'):
            if sha((attempt / 'worker_result.json').read_bytes()) != row['worker_result_sha256']:
                raise ValueError('Original worker evidence hash mismatch')
    return records


def acquire_lock(output, recover):
    path = output / '.runner.lock'
    if path.exists():
        saved = read_json(path)
        if same_process_alive(saved['identity']):
            raise ValueError('This output directory already has a live runner; do not start another')
        if not recover:
            raise ValueError('Stale lock preserved; use --resume --recover-interrupted after checking stopped processes')
        target = output / 'recovery' / ('stale_lock_' + uuid.uuid4().hex + '.json')
        target.parent.mkdir(exist_ok=True)
        path.rename(target)
    write_new(path, {'identity': process_identity(os.getpid()), 'session': SESSION})
    return path


def recover_attempts(output, plan, records, allow):
    finalized = {(r['job_key'], r['attempt']) for r in records}
    keys = {job_key(plan, c) for c in plan['cases']}
    for attempt in sorted((output / 'jobs').glob('*/attempt-*')):
        if attempt.parent.name not in keys:
            raise ValueError('Unplanned attempt directory; preserve and inspect')
        if (attempt.parent.name, int(attempt.name.split('-')[1])) in finalized or (attempt / 'recovery.json').exists():
            continue
        saved_process = attempt / 'worker_process.json'
        if saved_process.exists() and same_process_alive(read_json(saved_process)['identity']):
            raise ValueError('Previous attempt still has a live worker; recovery refused')
        if not allow:
            raise ValueError('Unfinalized attempt preserved: ' + str(attempt) + '; use --resume --recover-interrupted')
        completed = attempt / 'controller_result.json'
        if completed.exists():
            record = read_json(completed)
            append(output / 'results.jsonl', record)
            validate_records(output, plan)
            event(output, 'final_controller_record_recovered', attempt=attempt.relative_to(output).as_posix())
            continue
        inventory = {p.name: sha(p.read_bytes()) for p in attempt.iterdir() if p.is_file()}
        write_new(attempt / 'recovery.json', {'classification': 'interrupted_no_solver_outcome_inferred',
                  'original_file_hashes': inventory, 'new_attempt_full_budget_seconds': plan['timeout_seconds'], 'prior_time_charged': 0})


def heartbeat(output, plan, phase, final_count, case=None, launched=None, solve_seen=None, worker=None, available=None, usage=None):
    now = time.perf_counter()
    view = {'phase': phase, 'stamp': stamp(), 'planned': len(plan['cases']), 'final_records': final_count,
            'pending': len(plan['cases']) - final_count, 'case_id': case['case_id'] if case else None,
            'solver': 'OpenCAD', 'timeout_seconds': plan['timeout_seconds'],
            'attempt_wall_seconds': now-launched if launched else None,
            'solve_watchdog_elapsed_seconds': now-solve_seen if solve_seen else None,
            'worker_identity': worker.identity if worker else None, 'available_memory': available,
            'resource_usage': usage, 'runner_pid': os.getpid()}
    derived(output / 'heartbeat.json', view)


def execute(plan, case, output, final_count):
    key = job_key(plan, case)
    parent = output / 'jobs' / key
    number = max((int(p.name.split('-')[1]) for p in parent.glob('attempt-*')), default=0) + 1
    attempt = parent / f'attempt-{number:04d}'
    attempt.mkdir(parents=True, exist_ok=False)
    request = {'schema_version': 1, 'request_id': uuid.uuid4().hex, 'case_id': case['case_id'],
               'solver': 'OpenCAD', 'seed': plan['seed'], 'timeout_seconds': plan['timeout_seconds'],
               'input_path': str((ROOT / case['input_path']).resolve()), 'input_sha256': case['input_sha256'],
               'worker_result_path': str((attempt / 'worker_result.json').resolve())}
    write_new(attempt / 'request.json', request)
    write_new(attempt / 'attempt_start.json', {'fingerprint': plan['fingerprint'], 'stamp': stamp(), 'prior_time_charged': 0})
    command = [plan['kernel'], '-noinit', '-script', str(ROOT / 'components/OpenCADWorker.wls'), '--', '--request', str(attempt / 'request.json')]
    event(output, 'attempt_started', case_id=case['case_id'], attempt=number)
    process = None
    launched = time.perf_counter()
    solve_seen = finish_seen = None
    trigger = {}
    usage = {}
    warning = False
    next_heartbeat = 0
    try:
        with (attempt / 'stdout.log').open('xb') as stdout, (attempt / 'stderr.log').open('xb') as stderr:
            process = WorkerProcess(command, stdout, stderr, ROOT, plan['cpu_index'], plan['job_private_commit_limit_bytes'])
            write_new(attempt / 'worker_process.json', {'identity': process.identity, 'command': command, 'stamp': stamp()})
            while True:
                now = time.perf_counter()
                for name in ('solve_started', 'solve_finished'):
                    marker = attempt / (name + '.json')
                    if marker.exists() and ((name == 'solve_started' and solve_seen is None) or (name == 'solve_finished' and finish_seen is None)):
                        data = read_json(marker)
                        if data.get('request_id') != request['request_id']:
                            raise ValueError('Phase marker identity mismatch')
                        if name == 'solve_started': solve_seen = now
                        else: finish_seen = now
                usage = process.sample()
                if usage['memory_limit_events']:
                    trigger = {'kind': 'declared_job_memory_limit'}
                    break
                if process.poll() is not None:
                    break
                available = memory_available_mb()
                if available['available_commit_mb'] < plan['reserve_commit_mb']:
                    trigger = {'kind': 'host_resource_guard', 'available_memory': available}
                    break
                if available['available_physical_mb'] < 1024 and not warning:
                    warning = True
                    event(output, 'physical_memory_warning', available=available)
                    print('MEMORY WARNING: physical RAM low; continuing with available commit.', flush=True)
                if solve_seen is None and now-launched > plan['startup_grace_seconds']:
                    trigger = {'kind': 'startup_deadline'}
                    break
                if solve_seen is not None and finish_seen is None and now-solve_seen > plan['timeout_seconds'] + plan['watchdog_grace_seconds']:
                    trigger = {'kind': 'solve_watchdog', 'observed_solve_elapsed_seconds': now-solve_seen}
                    break
                if finish_seen is not None and now-finish_seen > plan['finalization_grace_seconds']:
                    trigger = {'kind': 'finalization_deadline'}
                    break
                if now >= next_heartbeat:
                    phase = 'startup' if solve_seen is None else ('finalizing' if finish_seen else 'solving')
                    heartbeat(output, plan, phase, final_count, case, launched, solve_seen, process, available, usage)
                    next_heartbeat = now + 5
                time.sleep(.2)
    except KeyboardInterrupt:
        trigger = {'kind': 'user_interruption'}
    finally:
        if process is not None:
            process.close()
    wall = time.perf_counter()-launched
    code = process.poll() if process is not None else None
    write_new(attempt / 'resource_usage.json', {'resource_usage': usage, 'termination_trigger': trigger,
              'worker_wall_seconds': wall, 'worker_exit_code': code})
    if trigger.get('kind') in {'host_resource_guard', 'startup_deadline', 'user_interruption'}:
        write_new(attempt / 'interruption.json', {**trigger, 'stamp': stamp(), 'worker_wall_seconds': wall,
                  'worker_exit_code': code, 'solver_outcome_inferred': False, 'resource_usage': usage})
        event(output, 'campaign_interrupted', case_id=case['case_id'], **trigger)
        return None
    result_path = attempt / 'worker_result.json'
    result_hash = sha(result_path.read_bytes()) if result_path.exists() else None
    if result_path.exists():
        try:
            worker = read_json(result_path)
            if not isinstance(worker, dict): raise ValueError('Worker result must be an object')
        except (ValueError, UnicodeError) as exc:
            worker = {'actual_status': 'error', 'solve_seconds': 0., 'solve_seconds_measured': False,
                      'failure_kind': 'worker_protocol_error', 'reason': str(exc)}
    elif trigger.get('kind') == 'solve_watchdog':
        worker = {'actual_status': 'timeout', 'solve_seconds': plan['timeout_seconds'],
                  'solve_time_is_budget_bound_not_measured': True, 'failure_kind': 'external_solve_watchdog'}
    else:
        worker = {'actual_status': 'error', 'solve_seconds': 0., 'solve_seconds_measured': False,
                  'failure_kind': trigger.get('kind', 'worker_exit'), 'worker_exit_code': code}
    try:
        effective, validation = validate_worker(worker, case, plan, request['request_id'], code)
    except (ValueError, KeyError, TypeError, ZeroDivisionError) as exc:
        received = worker
        worker = {'actual_status': 'error', 'solve_seconds': 0., 'solve_seconds_measured': False,
                  'failure_kind': 'worker_protocol_error', 'reason': str(exc), 'received_worker_result': received}
        effective, validation = validate_worker(worker, case, plan, request['request_id'], code)
    if trigger.get('kind') == 'declared_job_memory_limit':
        effective = 'memout'
    record = {'schema_version': 1, 'fingerprint': plan['fingerprint'], 'job_key': key, 'attempt': number,
              'request_id': request['request_id'], 'solver': 'OpenCAD', 'case_id': case['case_id'],
              'benchmark': case['benchmark_group'], 'expected_status': case['expected_status'], 'input_sha256': case['input_sha256'],
              'worker_result': worker, 'worker_result_sha256': result_hash, 'worker_exit_code': code,
              'actual_status': worker['actual_status'], 'effective_status': effective,
              'count_as_solved': effective in {'sat', 'unsat'}, 'validation': validation,
              'solve_seconds': worker['solve_seconds'], 'worker_wall_seconds': wall,
              'termination_trigger': trigger, 'resource_usage': usage,
              'attempt_directory': attempt.relative_to(output).as_posix(), 'completed': stamp()}
    write_new(attempt / 'controller_result.json', record)
    append(output / 'results.jsonl', record)
    event(output, 'attempt_finalized', case_id=case['case_id'], effective_status=effective)
    return record


def summarize(output, records=None):
    output = Path(output).resolve()
    plan = checked_plan(output)
    if records is None:
        records = validate_records(output, plan)
    summary_dir = output / 'summary'
    summary_dir.mkdir(exist_ok=True)
    fields = ['benchmark', 'planned', 'final_records', 'sat', 'unsat', 'solved', 'unknown', 'timeout', 'memout', 'error', 'conflict', 'invalid_model', 'pending']
    rows = []
    for group in plan['benchmarks']:
        subset = [r for r in records if r['benchmark'] == group]
        counts = Counter(r['effective_status'] for r in subset)
        planned = sum(c['benchmark_group'] == group for c in plan['cases'])
        row = {'benchmark': group, 'planned': planned, 'final_records': len(subset), 'solved': counts['sat']+counts['unsat'], 'pending': planned-len(subset)}
        row.update({name: counts[name] for name in fields if name not in row})
        rows.append(row)
    with (summary_dir / 'summary.csv').open('w', encoding='utf-8-sig', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader(); writer.writerows(rows)
    with (summary_dir / 'detail.csv').open('w', encoding='utf-8-sig', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=['case_id','benchmark','expected_status','effective_status','count_as_solved','solve_seconds','worker_wall_seconds','attempt','input_sha256','attempt_directory'], extrasaction='ignore')
        writer.writeheader(); writer.writerows(records)
    report = {'fingerprint': plan['fingerprint'], 'planned': len(plan['cases']), 'final_records': len(records),
              'pending': len(plan['cases'])-len(records), 'counts': dict(Counter(r['effective_status'] for r in records)),
              'results_sha256': sha((output / 'results.jsonl').read_bytes()) if (output / 'results.jsonl').exists() else None,
              'by_benchmark': rows}
    derived(summary_dir / 'summary.json', report)
    return report


def run(args):
    plan = make_plan(args)
    if args.dry_run:
        print(json.dumps({'planned': len(plan['cases']), 'by_benchmark': dict(Counter(c['benchmark_group'] for c in plan['cases'])),
                          'timeout_seconds': plan['timeout_seconds'], 'memory_gib': plan['job_private_commit_limit_bytes']/1024**3}, indent=2))
        return 0
    output = Path(args.output_dir or ROOT / ('results/opencad_' + args.benchmark.lower())).resolve()
    output.mkdir(parents=True, exist_ok=True)
    lock = acquire_lock(output, args.recover_interrupted)
    state = 'stopped'
    frozen = False
    records = None
    try:
        if (output / 'run_plan.json').exists():
            prior = checked_plan(output)
            if not args.resume or prior != plan:
                raise ValueError('Resume refused: saved plan/code/input/runtime/settings differ, or --resume is missing')
        else:
            allowed = {'.runner.lock'}
            if any(p.name not in allowed and not p.name.startswith('launcher_') for p in output.iterdir()):
                raise ValueError('Existing evidence without a matching plan; choose a new output directory')
            write_new(output / 'run_plan.json', plan)
        frozen = True
        if args.recover_interrupted:
            recover_tail(output)
        records = validate_records(output, plan)
        recover_attempts(output, plan, records, args.recover_interrupted)
        records = validate_records(output, plan)
        if any(r['effective_status'] in {'conflict', 'invalid_model'} for r in records):
            raise ValueError('Prior correctness conflict requires inspection; automatic continuation refused')
        done = {r['job_key'] for r in records}
        print(f'OpenCAD: {len(plan["cases"])} jobs; {len(done)} retained; serial fresh single-CPU kernels; solve budget {plan["timeout_seconds"]:g}s.', flush=True)
        for case in plan['cases']:
            if job_key(plan, case) in done:
                continue
            available = memory_available_mb()
            if available['available_commit_mb'] < plan['reserve_commit_mb']:
                event(output, 'campaign_interrupted', kind='host_resource_guard_before_launch', available_memory=available)
                state = 'interrupted'
                return 75
            print('START ' + case['case_id'] + ' OpenCAD', flush=True)
            record = execute(plan, case, output, len(done))
            if record is None:
                state = 'interrupted'
                print('Interrupted; evidence preserved. Inspect interruption.json before recovery.', flush=True)
                return 75
            done.add(record['job_key'])
            records.append(record)
            print(f'[{len(done)}/{len(plan["cases"])}] {case["case_id"]} OpenCAD: {record["effective_status"]}', flush=True)
            if record['effective_status'] in {'conflict', 'invalid_model'}:
                state = 'correctness_conflict'
                return 1
            summarize(output, records)
        state = 'completed'
        return 0
    finally:
        try:
            if frozen:
                report = summarize(output, records)
                heartbeat(output, plan, state, report['final_records'])
                print(json.dumps(report, indent=2), flush=True)
        finally:
            if lock.exists() and read_json(lock).get('session') == SESSION:
                lock.unlink()


def parser():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    doctor = commands.add_parser('doctor')
    doctor.add_argument('--wolfram-command')
    commands.add_parser('verify-inputs')
    summary = commands.add_parser('summarize')
    summary.add_argument('--output-dir', required=True)
    run_p = commands.add_parser('run')
    run_p.add_argument('--benchmark', choices=('All',)+GROUPS, default='All')
    run_p.add_argument('--wolfram-command')
    run_p.add_argument('--output-dir')
    run_p.add_argument('--timeout', type=float, default=60.)
    run_p.add_argument('--memory-gib', type=float, default=8.)
    run_p.add_argument('--reserve-mb', type=float, default=1024.)
    run_p.add_argument('--startup-grace', type=float, default=180.)
    run_p.add_argument('--seed', type=int, default=314159)
    run_p.add_argument('--cpu', type=int, default=0)
    run_p.add_argument('--case-id', action='append', default=[])
    run_p.add_argument('--max-cases', type=int)
    run_p.add_argument('--resume', action='store_true')
    run_p.add_argument('--recover-interrupted', action='store_true')
    run_p.add_argument('--dry-run', action='store_true')
    return parser


def main():
    args = parser().parse_args()
    try:
        if args.command == 'run':
            if args.recover_interrupted and not args.resume:
                raise ValueError('--recover-interrupted requires --resume')
            return run(args)
        if args.command == 'summarize':
            print(json.dumps(summarize(Path(args.output_dir)), indent=2)); return 0
        cases = load_cases()
        report = {'verified_inputs': len(cases), 'by_benchmark': dict(Counter(c['benchmark_group'] for c in cases))}
        if args.command == 'doctor':
            report['kernel'] = kernel_path(args.wolfram_command)
            report['runtime'] = probe_runtime(report['kernel'])
            report['available_memory'] = memory_available_mb()
        print(json.dumps(report, indent=2))
        return 0
    except KeyboardInterrupt:
        print('Interrupted; preserve the entire output directory.', file=sys.stderr); return 130
    except (ValueError, OSError, KeyError, TypeError, ZeroDivisionError) as exc:
        print('ERROR: ' + str(exc), file=sys.stderr); return 2


if __name__ == '__main__':
    raise SystemExit(main())
