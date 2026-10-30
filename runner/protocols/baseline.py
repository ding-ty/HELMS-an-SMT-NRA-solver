"""Measured independent baseline supervision and exact model checks."""
from __future__ import annotations

import argparse

from collections import Counter

import csv

from fractions import Fraction

import hashlib

import json

import math

import os

from pathlib import Path, PureWindowsPath

import platform

import re

import shutil

import subprocess

import sys

import tempfile

import time

import uuid

try:
    from .baseline_process import WorkerProcess, memory_available_mb, pid_alive
except ImportError:
    from baseline_process import WorkerProcess, memory_available_mb, pid_alive

ROOT = Path(__file__).resolve().parents[2]

SOLVERS = ('LiMbS', 'OpenCAD')

BENCHMARKS = ('SMTLIB', 'RandInst', 'SpecInst')

SESSION = uuid.uuid4().hex

ORIGIN = time.perf_counter()

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode('utf-8')

def stamp():
    return {'session': SESSION, 'elapsed_seconds': time.perf_counter() - ORIGIN}

def reject_nonfinite(token):
    raise ValueError('Non-finite JSON number: ' + token)

def read_json(path):
    return json.loads(Path(path).read_bytes(), parse_constant=reject_nonfinite)

def write_new_json(path, value):
    """Never overwrite an existing observation or attempt-sidecar file."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(json.dumps(value, indent=2, ensure_ascii=True, allow_nan=False).encode() + b'\n')
        stream.flush()
        os.fsync(stream.fileno())

def append_json(path, value):
    with Path(path).open('ab') as stream:
        stream.write(canonical(value) + b'\n')
        stream.flush()
        os.fsync(stream.fileno())

def read_journal(path):
    path = Path(path)
    if not path.exists():
        return []
    raw = path.read_bytes()
    if raw and not raw.endswith(b'\n'):
        raise ValueError('Journal lacks a complete final newline. Preserve it and use --resume --recover-interrupted.')
    records = []
    for number, line in enumerate(raw.splitlines(), 1):
        if not line:
            raise ValueError(f'Empty journal record at line{number}')
        try:
            record = json.loads(line, parse_constant=reject_nonfinite)
        except (ValueError, UnicodeError) as exc:
            raise ValueError(f'Malformed journal line{number}; source must be preserved') from exc
        if not isinstance(record, dict):
            raise ValueError('Journal records must be objects')
        records.append(record)
    return records

def load_manifest(path):
    rows = read_journal(path)
    seen = set()
    for row in rows:
        case = row.get('case_id')
        if case in seen or row.get('benchmark_group') not in BENCHMARKS or row.get('expected_status') not in {'sat', 'unsat', 'unknown'}:
            raise ValueError('Invalid/duplicate benchmark metadata')
        seen.add(case)
        relative = Path(row['input_path'])
        actual = (ROOT / relative).resolve()
        if relative.is_absolute() or not actual.is_relative_to(ROOT.resolve()):
            raise ValueError('Input path escapes package')
        if sha(actual.read_bytes()) != row['input_sha256']:
            raise ValueError('Input hash mismatch: ' + str(case))
    return rows

def kernel_path(command):
    value = command or os.environ.get('WOLFRAM_COMMAND') or shutil.which('math') or shutil.which('WolframKernel')
    if not value:
        raise ValueError('Set --wolfram-command to the activated Mathematica console kernel')
    result = Path(shutil.which(value) or value).resolve()
    if not result.is_file():
        raise ValueError('Kernel executable does not exist: ' + str(result))
    return str(result)

def probe_runtime(kernel):
    with tempfile.TemporaryDirectory(prefix='helms_baseline_probe_') as directory:
        script = Path(directory) / 'probe.wls'
        script.write_text('Print["BASELINE_RUNTIME_BEGIN"];\nPrint[ExportString[<|"wolfram_version"->$Version,"system_id"->$SystemID|>,"RawJSON"]];\nPrint["BASELINE_RUNTIME_END"];\nExit[0];\n', encoding='ascii')
        result = subprocess.run([kernel, '-noinit', '-script', str(script)], capture_output=True, timeout=60,
                                creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)
        text = result.stdout.decode('utf-8', errors='replace')
        match = re.search(r'BASELINE_RUNTIME_BEGIN\s*(.*?)\s*BASELINE_RUNTIME_END', text, re.S)
        if result.returncode or not match:
            raise ValueError('Mathematica startup/license probe failed: ' + (text + result.stderr.decode('utf-8', errors='replace'))[-1500:])
        return json.loads(match[1])

def choose_list(value, allowed):
    selected = list(allowed) if value.lower() == 'all' else [v.strip() for v in value.split(',')]
    if not selected or len(set(selected)) != len(selected) or set(selected) - set(allowed):
        raise ValueError('Select from: ' + ','.join(allowed))
    return selected

def worker_command(plan, request_path):
    return [plan['kernel'], '-noinit', '-script', plan['worker_script'], '--', '--request', str(request_path)]

def exact(node, model):
    op = node['op']
    if op == 'int': return Fraction(int(node['value']))
    if op == 'rat': return Fraction(int(node['numerator']), int(node['denominator']))
    if op == 'var': return model[node['name']]
    if op == 'add': return sum((exact(n, model) for n in node['args']), Fraction(0))
    if op == 'mul':
        value = Fraction(1)
        for n in node['args']: value *= exact(n, model)
        return value
    if op == 'pow' and type(node['exponent']) is int and node['exponent'] >= 0:
        return exact(node['base'], model) ** node['exponent']
    raise ValueError('Unsupported exact AST')

def validate_worker(worker, case, plan=None, exit_code=0, expected_solver=None, request_id=None):
    if not isinstance(worker, dict):
        raise ValueError('Worker result must be an object')
    actual = worker.get('actual_status')
    if actual not in {'sat', 'unsat', 'unknown', 'error', 'timeout'}:
        raise ValueError('Worker returned an invalid status')
    seconds = worker.get('solve_seconds')
    if type(seconds) not in (float, int) or not math.isfinite(seconds) or seconds < 0:
        raise ValueError('Worker returned invalid solve time')
    validation = {'expected_status_comparison': 'not_applicable'}
    effective = actual
    if actual == 'error' and worker.get('failure_kind') == 'invalid_model' and worker.get('reported_status') == 'sat':
        effective = 'invalid_model'
        validation['model'] = 'worker_original_formula_verification_failed'
    if actual == 'sat':
        data = read_json(ROOT / case['input_path'])
        values = worker.get('model_values')
        if not isinstance(values, dict) or set(values) != set(data['variables']):
            effective = 'invalid_model'
            validation['model'] = 'missing_or_incomplete'
        elif all(isinstance(v, str) and re.fullmatch(r'[+-]?\d+(?:/\d+)?', v) for v in values.values()):
            try:
                polys = [exact(p, {k: Fraction(v) for k, v in values.items()}) for p in data['polynomials']]
                valid = all(any(sign * polys[index - 1] > 0 for index, sign in clause) for clause in data['clauses'])
            except (ValueError, ZeroDivisionError, KeyError, TypeError):
                valid = False
            validation['model'] = 'independent_exact_rational_pass' if valid else 'independent_exact_rational_fail'
            if not valid: effective = 'invalid_model'
        else:
            # Algebraic Root expressions are retained as WL text, never eval'ed
            # in Python. Their validation tier is explicit and weaker than an
            # independent rational check.
            native = worker.get('model_validation', {})
            valid = isinstance(native, dict) and native.get('valid') is True and native.get('exact') is True
            validation['model'] = 'wolfram_exact_algebraic_pass' if valid else 'algebraic_validation_missing'
            if not valid: effective = 'invalid_model'
    if actual in {'sat', 'unsat'} and case['expected_status'] in {'sat', 'unsat'}:
        matches = actual == case['expected_status']
        validation['expected_status_comparison'] = 'matches_existing_evidence' if matches else 'conflict'
        if not matches: effective = 'conflict'
    validation['unsat_independently_reproved'] = False
    if plan is not None:
        controller_timeout = actual == 'timeout' and worker.get('controller_generated') is True
        if worker.get('runtime_identity') != plan['runtime'] and actual != 'error' and not controller_timeout:
            validation['protocol_error'] = 'worker_runtime_identity_mismatch'
            effective = 'error'
        if worker.get('input_sha256', case['input_sha256']) != case['input_sha256']:
            validation['protocol_error'] = 'worker_input_hash_mismatch'
            effective = 'error'
        if actual in {'sat', 'unsat'} and seconds > plan['timeout_seconds']:
            validation['solve_budget_exceeded_after_return'] = True
            if effective in {'sat', 'unsat'}:
                effective = 'timeout'
        if actual in {'sat', 'unsat'}:
            identities = {'case_id': case['case_id'], 'input_sha256': case['input_sha256']}
            if expected_solver is not None: identities['solver'] = expected_solver
            if request_id is not None: identities['request_id'] = request_id
            for field, expected in identities.items():
                if worker.get(field) != expected:
                    validation['protocol_error'] = 'worker_' + field + '_mismatch'
                    effective = 'error'
            if expected_solver == 'LiMbS' and worker.get('library_sha256') != plan['library_revision']['active_source_sha256']:
                validation['protocol_error'] = 'worker_library_sha256_mismatch'
                effective = 'error'
    if exit_code not in (0, None) and actual not in {'error', 'timeout'}:
        validation['protocol_error'] = 'worker_nonzero_exit_after_result'
        effective = 'error'
    return effective, validation

def event(output, name, **fields):
    append_json(output / 'attempt_events.jsonl', {'event': name, 'stamp': stamp(), **fields})

def memory_guard_reason(available, reserve_mb, system=None):
    if not available:
        return None
    system = system or platform.system()
    if system == 'Windows':
        if 'available_commit_mb' not in available:
            raise ValueError('Windows system commit availability is missing')
        exhausted = available['available_commit_mb'] < reserve_mb
    else:
        exhausted = min(available.values()) < reserve_mb
    return {'kind': 'host_resource_guard', 'available_memory': available} if exhausted else None

def execute_job(plan, case, job, output):
    parent = output / 'jobs' / job['job_key']
    prior_numbers = [int(p.name.split('-')[1]) for p in parent.glob('attempt-*') if p.is_dir()]
    number = max(prior_numbers, default=0) + 1
    attempt = parent / f'attempt-{number:04d}'
    attempt.mkdir(parents=True, exist_ok=False)
    request = {'schema_version': 1, 'request_id': uuid.uuid4().hex, 'case_id': case['case_id'], 'solver': job['solver'],
               'input_path': str((ROOT / case['input_path']).resolve()), 'input_sha256': case['input_sha256'],
               'seed': plan['seed'], 'timeout_seconds': plan['timeout_seconds'],
               'worker_result_path': str((attempt / 'worker_result.json').resolve())}
    request_path = attempt / 'request.json'
    write_new_json(request_path, request)
    write_new_json(attempt / 'attempt_start.json', {'fingerprint': plan['fingerprint'], 'job_key': job['job_key'],
                   'attempt': number, 'stamp': stamp(), 'timeout_seconds': plan['timeout_seconds'], 'prior_time_charged': 0})
    command = worker_command(plan, request_path)
    event(output, 'attempt_started', job_key=job['job_key'], attempt=number, case_id=case['case_id'], solver=job['solver'])
    process = None
    launched = time.perf_counter()
    solve_seen, finish_seen = None, None
    interruption, forced_timeout, finalization_error = None, False, False
    physical_warning_seen = False
    try:
        with (attempt / 'stdout.log').open('xb') as stdout, (attempt / 'stderr.log').open('xb') as stderr:
            process = WorkerProcess(command, stdout, stderr, ROOT, plan['cpu_index'])
            write_new_json(attempt / 'worker_process.json', {'pid': process.pid, 'stamp': stamp(), 'command': command})
            while process.poll() is None:
                now = time.perf_counter()
                if solve_seen is None and (attempt / 'solve_started.json').exists(): solve_seen = now
                if finish_seen is None and (attempt / 'solve_finished.json').exists(): finish_seen = now
                available = memory_available_mb()
                interruption = memory_guard_reason(available, plan['reserve_mb'], plan['host']['system'])
                if interruption:
                    break
                if (plan['host']['system'] == 'Windows' and not physical_warning_seen and
                        available.get('available_physical_mb', float('inf')) < plan['reserve_mb']):
                    physical_warning_seen = True
                    event(output, 'physical_memory_pressure_warning', job_key=job['job_key'], attempt=number,
                          available_memory=available, action='continue_with_available_system_commit')
                    print('MEMORY WARNING: physical RAM is low; system commit remains available, continuing.', flush=True)
                if solve_seen is None and now - launched > plan['startup_grace_seconds']:
                    interruption = {'kind': 'startup_deadline', 'startup_elapsed_seconds': now - launched}
                    break
                if solve_seen is not None and finish_seen is None and now - solve_seen > plan['timeout_seconds'] + plan['watchdog_grace_seconds']:
                    forced_timeout = True
                    break
                if finish_seen is not None and now - finish_seen > plan['finalization_grace_seconds']:
                    finalization_error = True
                    break
                time.sleep(0.2)
    except KeyboardInterrupt:
        interruption = {'kind': 'user_interruption'}
    finally:
        if process is not None: process.close()
    wall = time.perf_counter() - launched
    exit_code = process.poll() if process is not None else None
    if interruption:
        write_new_json(attempt / 'interruption.json', {**interruption, 'stamp': stamp(), 'worker_wall_seconds': wall,
                       'worker_exit_code': exit_code, 'solver_outcome_inferred': False})
        event(output, 'campaign_interrupted', job_key=job['job_key'], attempt=number, **interruption)
        return None
    result_path = attempt / 'worker_result.json'
    if result_path.exists():
        try:
            worker = read_json(result_path)
            if not isinstance(worker, dict):
                raise ValueError('Worker JSON is not an object')
        except (ValueError, UnicodeError) as exc:
            worker = {'actual_status': 'error', 'solve_seconds': 0.0, 'solve_seconds_measured': False,
                      'failure_kind': 'worker_protocol_error', 'reason': str(exc),
                      'unparsed_worker_result_sha256': sha(result_path.read_bytes()),
                      'original_worker_result_preserved': True}
    elif forced_timeout:
        worker = {'actual_status': 'timeout', 'solve_seconds': plan['timeout_seconds'],
                  'failure_kind': 'external_solve_watchdog', 'reason': 'No worker response after a full solve budget plus watchdog grace',
                  'solve_time_is_budget_bound_not_measured': True, 'controller_generated': True}
    else:
        worker = {'actual_status': 'error', 'solve_seconds': 0.0, 'solve_seconds_measured': False,
                  'failure_kind': 'finalization_deadline' if finalization_error else 'worker_exit',
                  'reason': 'Worker did not produce a final result', 'worker_exit_code': exit_code}
    try:
        effective, validation = validate_worker(worker, case, plan, exit_code, job['solver'], request['request_id'])
    except (ValueError, TypeError, KeyError) as exc:
        received = worker
        worker = {'actual_status': 'error', 'solve_seconds': 0.0, 'solve_seconds_measured': False,
                  'failure_kind': 'worker_protocol_error', 'reason': str(exc),
                  'received_worker_result': received, 'original_worker_result_preserved': True}
        effective, validation = validate_worker(worker, case, plan, exit_code, job['solver'], request['request_id'])
        validation['protocol_error'] = str(exc)
    record = {'schema_version': 1, 'fingerprint': plan['fingerprint'], 'job_key': job['job_key'], 'attempt': number,
              'request_id': request['request_id'],
              'case_id': case['case_id'], 'benchmark': case['benchmark_group'], 'family': case['family'],
              'expected_status': case['expected_status'], 'input_path': case['input_path'], 'input_sha256': case['input_sha256'],
              'solver': job['solver'], 'seed': plan['seed'], 'timeout_seconds': plan['timeout_seconds'],
              'runtime_identity': plan['runtime'], 'source_fingerprint': sha(canonical(plan['sources'])),
              'worker_result': worker, 'actual_status': worker.get('actual_status', 'error'),
              'effective_status': effective, 'count_as_solved': effective in {'sat', 'unsat'}, 'validation': validation,
              'solve_seconds': worker.get('solve_seconds'), 'worker_wall_seconds': wall, 'worker_exit_code': exit_code,
              'attempt_directory': attempt.relative_to(output).as_posix(), 'completed': stamp(),
              'timing_basis': plan['timing_basis']}
    write_new_json(attempt / 'controller_result.json', record)
    append_json(output / 'results.jsonl', record)
    event(output, 'attempt_finalized', job_key=job['job_key'], attempt=number, actual_status=record['actual_status'], effective_status=effective)
    return record
