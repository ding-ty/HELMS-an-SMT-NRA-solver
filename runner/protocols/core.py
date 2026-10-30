#!/usr/bin/env python3
"""Portable, deliberately serial experiment runner (Python standard library only)."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from typing import Any

SCHEMA_VERSION = 1
PACKAGE_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOLVERS = ("HELMS", "2D-LS", "V1", "V2", "V3", "V4", "V5", "LS-WL")
SOLVERS = (*DEFAULT_SOLVERS, "1D-control", "MCSAT-core", "OpenCAD")
SAT_ONLY_SOLVERS = {"2D-LS", "LS-WL", "1D-control"}
ACTUAL_STATUSES = {"sat", "unsat", "unknown", "error", "timeout"}
EVENT_SESSION = uuid.uuid4().hex
EVENT_ORIGIN = time.perf_counter()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
                      allow_nan=False).encode("utf-8")


def digest_object(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def event_stamp() -> str:
    """Order events without recording a calendar date or machine uptime.

    A fresh opaque session distinguishes resumes. The *_at schema fields
    contain this relative marker, never a UTC or local wall-clock timestamp.
    Solver durations still use the existing independent timing measurements.
    """
    return f"session:{EVENT_SESSION};elapsed_seconds:{time.perf_counter() - EVENT_ORIGIN:.6f}"


def wolfram_string(value: str) -> str:
    """ASCII WL string literal, independent of Windows script-file encoding."""
    pieces = []
    escapes = {'"': '\\"', "\\": "\\\\", "\n": "\\n", "\r": "\\r", "\t": "\\t"}
    for character in value:
        number = ord(character)
        if character in escapes:
            pieces.append(escapes[character])
        elif number < 32 or number > 126:
            pieces.append(f"\\:{number:04x}" if number <= 0xffff else f"\\|{number:06x}")
        else:
            pieces.append(character)
    return '"' + "".join(pieces) + '"'


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False,
                                    allow_nan=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def read_json(path: Path) -> Any:
    with path.open(encoding="utf-8-sig") as handle:
        return json.load(handle)


def load_manifest(path: Path) -> list[dict[str, Any]]:
    """Resolve paths relative to the package root, and verify available inputs."""
    path = path.resolve()
    if path.suffix.lower() == ".csv":
        with path.open(encoding="utf-8-sig", newline="") as handle:
            raw_rows = list(csv.DictReader(handle))
    else:
        with path.open(encoding="utf-8-sig") as handle:
            raw_rows = [json.loads(line) for line in handle if line.strip()]
    rows = []
    seen = set()
    for number, source in enumerate(raw_rows, 1):
        if not isinstance(source, dict):
            raise ValueError(f"manifest record {number} is not an object")
        row = dict(source)
        case_id = row.get("case_id")
        if not isinstance(case_id, str) or not case_id or case_id in seen:
            raise ValueError(f"manifest record {number}: missing or duplicate case_id {case_id!r}")
        seen.add(case_id)
        explicit = row.get("expected_status")
        expected = str(explicit if explicit is not None else "unknown").strip().lower()
        if expected not in {"sat", "unsat", "unknown"}:
            raise ValueError(f"{case_id}: invalid expected_status {expected!r}")
        row["expected_status"] = expected
        row["explicit_expected_status"] = expected if explicit is not None else None
        row["expected_status_source"] = "manifest_expected_status" if explicit is not None else "unconfirmed_hint_or_unspecified"
        row["benchmark"] = str(row.get("benchmark_group", row.get("benchmark", "unspecified")))
        row["family"] = str(row.get("family", "unspecified"))
        input_value = row.get("input_path")
        if not input_value or row.get("availability") == "missing":
            row["input_path"] = None
            row["availability"] = "missing"
        else:
            input_path = Path(input_value)
            if not input_path.is_absolute():
                input_path = PACKAGE_ROOT / input_path
            input_path = input_path.resolve()
            if not input_path.is_file():
                raise ValueError(f"{case_id}: input file does not exist: {input_path}")
            actual_digest = sha256_file(input_path)
            declared_digest = row.get("input_sha256")
            if not isinstance(declared_digest, str) or declared_digest.lower() != actual_digest:
                raise ValueError(f"{case_id}: input_sha256 missing or does not match {input_path}")
            row["input_path"] = str(input_path)
            row["input_sha256"] = actual_digest
            row["availability"] = "available"
        rows.append(row)
    if not rows:
        raise ValueError("manifest has no cases")
    return rows


def build_job_selection(cases: list[dict[str, Any]], solvers: list[str], policy: str
                        ) -> tuple[list[dict[str, Any]], list[dict[str, str]]]:
    eligibility, jobs = [], []
    for case in cases:
        status = case.get("explicit_expected_status")
        for solver in solvers:
            reason = "eligible"
            if case["availability"] != "available":
                reason = "missing_input"
            elif policy == "paper" and status not in {"sat", "unsat"}:
                reason = "unconfirmed_status"
            elif policy == "paper" and solver in SAT_ONLY_SOLVERS and status != "sat":
                reason = "unsat_not_applicable_to_sat_only_mode"
            eligible = reason == "eligible"
            entry = {"case_id": case["case_id"], "solver": solver,
                     "eligible": eligible, "reason": reason}
            eligibility.append(entry)
            if eligible:
                jobs.append({"case_id": case["case_id"], "solver": solver})
    return eligibility, jobs


def get_eligibility(plan: dict[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    """Old plans retain their original all-pairs semantics when inspected."""
    pairs = [(case["case_id"], solver) for case in plan["cases"] for solver in plan["solvers"]]
    if "eligibility" not in plan:
        return {key: {"case_id": key[0], "solver": key[1], "eligible": True,
                      "reason": "all_pairs_plan"} for key in pairs}
    entries = plan["eligibility"]
    if not isinstance(entries, list) or len(entries) != len(pairs):
        raise ValueError("plan eligibility must describe every selected case/solver pair")
    result = {}
    for entry in entries:
        if not isinstance(entry, dict) or type(entry.get("eligible")) is not bool or not isinstance(entry.get("reason"), str):
            raise ValueError("plan has an invalid eligibility entry")
        key = (entry.get("case_id"), entry.get("solver"))
        if key in result:
            raise ValueError("plan has duplicate eligibility entries")
        result[key] = entry
    if set(result) != set(pairs):
        raise ValueError("plan eligibility references missing or unplanned pairs")
    expected_jobs = [{"case_id": case_id, "solver": solver} for case_id, solver in pairs
                     if result[(case_id, solver)]["eligible"]]
    if plan.get("jobs") != expected_jobs:
        raise ValueError("plan jobs do not match its eligibility matrix")
    if plan.get("case_policy") in {"paper", "all"}:
        expected_matrix, _ = build_job_selection(plan["cases"], plan["solvers"], plan["case_policy"])
        if entries != expected_matrix:
            raise ValueError("plan eligibility does not implement its declared case policy")
    return result


def runtime_prefix(args: argparse.Namespace) -> list[str]:
    command = args.wolfram_command
    if not command:
        command = os.environ.get("WOLFRAM_COMMAND")
    if not command:
        candidates = ("wolframscript", "WolframKernel", "MathKernel", "math")
        command = next((found for name in candidates if (found := shutil.which(name))), None)
    if not command:
        return []
    resolved = shutil.which(command)
    if resolved:
        command = str(Path(resolved).resolve())
    elif Path(command).is_file():
        command = str(Path(command).resolve())
    extra = json.loads(args.runtime_args)
    if not isinstance(extra, list) or any(not isinstance(value, str) for value in extra):
        raise ValueError("--runtime-args must be a JSON array of strings")
    extra.extend(args.runtime_arg)
    return [command, *extra]


def code_fingerprints(entrypoint: Path, extra_paths: list[str]) -> list[dict[str, str]]:
    paths = {entrypoint.resolve(), Path(__file__).resolve()}
    summary = Path(__file__).with_name("summary.py")
    if summary.exists():
        paths.add(summary.resolve())
    for directory in (PACKAGE_ROOT / "components", PACKAGE_ROOT / "solvers"):
        if directory.exists():
            paths.update(p.resolve() for p in directory.rglob("*")
                         if p.is_file() and p.suffix.lower() in {".wl", ".wls", ".m"})
    paths.update(p.resolve() for p in (PACKAGE_ROOT / "runner").rglob("*.py"))
    for value in extra_paths:
        candidate = Path(value).resolve()
        if candidate.is_dir():
            paths.update(p.resolve() for p in candidate.rglob("*") if p.is_file())
        else:
            paths.add(candidate)
    result = []
    for path in sorted(paths, key=str):
        if not path.is_file():
            raise ValueError(f"code file does not exist: {path}")
        result.append({"path": str(path), "sha256": sha256_file(path)})
    return result


def make_plan(args: argparse.Namespace) -> dict[str, Any]:
    manifest_path = Path(args.manifest).resolve()
    all_cases = load_manifest(manifest_path)
    cases = all_cases
    if args.case_id:
        wanted = set(args.case_id)
        cases = [row for row in cases if row["case_id"] in wanted]
        missing = wanted - {row["case_id"] for row in cases}
        if missing:
            raise ValueError(f"case IDs not found: {sorted(missing)}")
    if args.benchmark:
        wanted_benchmarks = set(args.benchmark)
        cases = [row for row in cases if row["benchmark"] in wanted_benchmarks]
    if args.max_cases is not None:
        if args.max_cases < 1:
            raise ValueError("--max-cases must be positive")
        cases = cases[:args.max_cases]
    if not cases:
        raise ValueError("case selection is empty")
    solvers = [value.strip() for value in args.solvers.split(",") if value.strip()]
    if not solvers or len(solvers) != len(set(solvers)) or any(s not in SOLVERS for s in solvers):
        raise ValueError(f"--solvers must contain distinct names from {', '.join(SOLVERS)}")
    eligibility, jobs = build_job_selection(cases, solvers, args.case_policy)
    if not jobs:
        reasons: dict[str, int] = {}
        for entry in eligibility:
            reasons[entry["reason"]] = reasons.get(entry["reason"], 0) + 1
        raise ValueError(f"no eligible jobs under case policy {args.case_policy!r}; excluded pairs: {reasons}")
    if args.timeout <= 0 or not math.isfinite(args.timeout):
        raise ValueError("--timeout must be finite and positive")
    if args.startup_grace <= 0 or not math.isfinite(args.startup_grace):
        raise ValueError("--startup-grace must be finite and positive")
    entrypoint = Path(args.entrypoint).resolve()
    config_path = Path(args.config).resolve() if args.config else None
    config = read_json(config_path) if config_path else {}
    if not isinstance(config, dict):
        raise ValueError("configuration must be a JSON object")
    runtime = runtime_prefix(args)
    identity = None if args.dry_run else verified_runtime_identity(args)
    payload = {
        "schema_version": SCHEMA_VERSION,
        "manifest_path": str(manifest_path),
        "manifest_sha256": sha256_file(manifest_path),
        "cases": cases,
        "solvers": solvers,
        "case_policy": args.case_policy,
        "eligibility": eligibility,
        "jobs": jobs,
        "seed": args.seed,
        "timeout_seconds": args.timeout,
        "startup_grace_seconds": args.startup_grace,
        "entrypoint": str(entrypoint),
        "runtime_command": runtime,
        "runtime_identity": identity,
        "runtime_executable_sha256": sha256_file(Path(runtime[0])) if runtime and Path(runtime[0]).is_file() else None,
        "launch_mode": args.launch_mode,
        "configuration": config,
        "configuration_path": str(config_path) if config_path else None,
        "configuration_sha256": sha256_file(config_path) if config_path else digest_object(config),
        "code": code_fingerprints(entrypoint, args.code),
        "python_version": sys.version,
        "runner_platform": sys.platform,
    }
    return {**payload, "fingerprint": digest_object(payload), "created_at": event_stamp()}


def worker_command(plan: dict[str, Any], request_path: Path) -> list[str]:
    switch = "-file" if plan["launch_mode"] == "file" else "-script"
    separator = ["--"] if plan["launch_mode"] == "script" else []
    return [*plan["runtime_command"], switch, plan["entrypoint"], *separator,
            "--request", str(request_path)]


def finite_nonnegative(value: Any) -> bool:
    return (isinstance(value, (float, int)) and not isinstance(value, bool)
            and math.isfinite(value) and value >= 0)


def normalize_worker_result(result: Any, timeout: float) -> dict[str, Any]:
    if not isinstance(result, dict):
        return {"actual_status": "error", "failure_kind": "invalid_worker_result",
                "reason": "worker result is not a JSON object"}
    status = result.get("actual_status")
    if not isinstance(status, str) or status.lower() not in ACTUAL_STATUSES:
        return {"actual_status": "error", "failure_kind": "invalid_worker_status",
                "reason": f"unsupported actual_status: {status!r}", "worker_result": result}
    status = status.lower()
    normalized = dict(result)
    normalized["actual_status"] = status
    solve = result.get("solve_seconds")
    startup = result.get("startup_seconds")
    # Successful claims require actual solver timing; startup is always separate.
    if status in {"sat", "unsat"} and not finite_nonnegative(solve):
        normalized.update(actual_status="error", failure_kind="invalid_solver_timing",
                          reason="SAT/UNSAT result is missing finite nonnegative solve_seconds")
    elif solve is not None and not finite_nonnegative(solve):
        normalized.update(actual_status="error", failure_kind="invalid_solver_timing",
                          reason="solve_seconds is invalid")
    elif status in {"sat", "unsat"} and not finite_nonnegative(startup):
        normalized.update(actual_status="error", failure_kind="invalid_startup_timing",
                          reason="SAT/UNSAT result is missing finite nonnegative startup_seconds")
    elif startup is not None and not finite_nonnegative(startup):
        normalized.update(actual_status="error", failure_kind="invalid_startup_timing",
                          reason="startup_seconds is invalid")
    elif solve is not None and solve > timeout:
        normalized["reported_status"] = status
        normalized.update(actual_status="timeout", failure_kind="solver_time_limit",
                          reason="worker solve_seconds exceeds the solver time limit")
    return normalized


def terminate_process_tree(process: subprocess.Popen[Any]) -> None:
    """Terminate only the new process tree belonging to this one worker."""
    if os.name == "nt":
        subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    try:
        process.kill()
    except ProcessLookupError:
        pass
    process.wait()


def execute_job(plan: dict[str, Any], case: dict[str, Any], solver: str,
                output_dir: Path, attempt: int) -> dict[str, Any]:
    job_key = digest_object({"fingerprint": plan["fingerprint"],
                             "case_id": case["case_id"], "solver": solver})
    job_dir = output_dir / "jobs" / job_key[:24] / f"attempt-{attempt:04d}"
    job_dir.mkdir(parents=True, exist_ok=False)
    request_path = job_dir / "request.json"
    result_path = job_dir / "worker_result.json"
    stdout_path = job_dir / "stdout.log"
    stderr_path = job_dir / "stderr.log"
    record = {
        "schema_version": SCHEMA_VERSION, "fingerprint": plan["fingerprint"],
        "job_key": job_key, "attempt": attempt, "case_id": case["case_id"],
        "benchmark": case["benchmark"], "family": case["family"],
        "expected_status": case["expected_status"], "input_path": case["input_path"],
        "input_sha256": case.get("input_sha256"), "solver": solver,
        "seed": plan["seed"], "timeout_seconds": plan["timeout_seconds"],
        "configuration_sha256": plan["configuration_sha256"],
        "code_fingerprint": digest_object(plan["code"]),
        "runtime_identity": plan.get("runtime_identity"),
        "case_policy": plan.get("case_policy", "all-pairs"),
        "started_at": event_stamp(), "request_path": str(request_path),
        "worker_result_path": str(result_path), "stdout_log": str(stdout_path),
        "stderr_log": str(stderr_path),
    }
    # Do not provide the expected result to the solver.
    request = {
        "schema_version": SCHEMA_VERSION, "fingerprint": plan["fingerprint"],
        "case_id": case["case_id"], "input_path": case["input_path"],
        "input_sha256": case.get("input_sha256"), "solver": solver,
        "seed": plan["seed"], "timeout_seconds": plan["timeout_seconds"],
        "worker_result_path": str(result_path),
        "worker_config": plan["configuration"].get("worker", plan["configuration"]),
        "package_root": str(PACKAGE_ROOT),
        "code": plan["code"],
    }
    write_json(request_path, request)
    started = time.monotonic()
    if case["availability"] == "missing":
        stdout_path.touch()
        stderr_path.write_text("No benchmark input is available for this manifest entry.\n", encoding="utf-8")
        result = {"actual_status": "error", "failure_kind": "missing_input",
                  "reason": "manifest entry has availability=missing", "solve_seconds": None,
                  "startup_seconds": None}
    else:
        command = worker_command(plan, request_path)
        record["command"] = command
        with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
            process = None
            try:
                options: dict[str, Any] = {"stdout": stdout, "stderr": stderr,
                                           "cwd": str(PACKAGE_ROOT), "stdin": subprocess.DEVNULL}
                if os.name == "nt":
                    options["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.CREATE_NO_WINDOW
                else:
                    options["start_new_session"] = True
                process = subprocess.Popen(command, **options)
                process.wait(timeout=plan["timeout_seconds"] + plan["startup_grace_seconds"])
                record["worker_exit_code"] = process.returncode
                if process.returncode != 0:
                    result = {"actual_status": "error", "failure_kind": "worker_exit",
                              "reason": f"worker exited with code {process.returncode}"}
                    if result_path.is_file():
                        try:
                            result["worker_result"] = read_json(result_path)
                        except (ValueError, OSError):
                            pass
                elif not result_path.is_file():
                    result = {"actual_status": "error", "failure_kind": "missing_worker_result",
                              "reason": "worker exited without writing its result JSON"}
                else:
                    try:
                        result = normalize_worker_result(read_json(result_path), plan["timeout_seconds"])
                    except (ValueError, OSError) as exc:
                        result = {"actual_status": "error", "failure_kind": "invalid_worker_result",
                                  "reason": str(exc)}
            except subprocess.TimeoutExpired:
                if process is not None:
                    terminate_process_tree(process)
                result = {"actual_status": "timeout", "failure_kind": "process_wall_timeout",
                          "reason": "worker exceeded solve timeout plus startup grace",
                          "solve_seconds": None, "startup_seconds": None}
            except OSError as exc:
                result = {"actual_status": "error", "failure_kind": "worker_launch", "reason": str(exc)}
            except BaseException:
                if process is not None and process.poll() is None:
                    terminate_process_tree(process)
                raise
    record["worker_result"] = result
    metadata = result.get("solver_metadata")
    expected_identity = plan.get("runtime_identity")
    if expected_identity and (result.get("actual_status") in {"sat", "unsat"} or isinstance(metadata, dict)):
        if not isinstance(metadata, dict) or any(metadata.get(key) != value for key, value in expected_identity.items()):
            result = {**result, "reported_status": result.get("actual_status"),
                      "actual_status": "error", "failure_kind": "runtime_identity_mismatch",
                      "reason": "worker Wolfram version/SystemID differs from the preflight-verified run plan"}
    for field in ("actual_status", "solve_seconds", "startup_seconds", "stage", "reason",
                  "failure_kind", "reported_status", "solver_metadata"):
        if field in result:
            record[field] = result[field]
    record["worker_wall_seconds"] = time.monotonic() - started
    record["finished_at"] = event_stamp()
    expected = case["expected_status"]
    conflict = (record["actual_status"] in {"sat", "unsat"} and expected in {"sat", "unsat"}
                and record["actual_status"] != expected)
    record["validation_conflict"] = conflict
    record["effective_status"] = "conflict" if conflict else record["actual_status"]
    record["count_as_solved"] = record["actual_status"] in {"sat", "unsat"} and not conflict
    return record


def read_results(path: Path, fingerprint: str) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    records = []
    with path.open(encoding="utf-8") as handle:
        for number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except ValueError as exc:
                raise ValueError(f"{path}:{number}: incomplete or invalid JSON; preserve and inspect this run") from exc
            if not isinstance(record, dict):
                raise ValueError(f"{path}:{number}: record is not a JSON object")
            if record.get("fingerprint") != fingerprint:
                raise ValueError(f"{path}:{number}: result fingerprint differs from this exact experiment")
            records.append(record)
    return records


def next_attempt(output_dir: Path, fingerprint: str, case_id: str, solver: str,
                 previous: dict[str, Any] | None) -> int:
    """Retain orphaned logs from interrupted processes; never overwrite an attempt."""
    job_key = digest_object({"fingerprint": fingerprint, "case_id": case_id, "solver": solver})
    job_dir = output_dir / "jobs" / job_key[:24]
    maximum = int(previous["attempt"]) if previous else 0
    if job_dir.exists():
        for path in job_dir.glob("attempt-*"):
            try:
                maximum = max(maximum, int(path.name.split("-", 1)[1]))
            except ValueError:
                continue
    return maximum + 1


def run(args: argparse.Namespace) -> int:
    plan = make_plan(args)
    if args.dry_run:
        printable = {
            "dry_run": True, "fingerprint": plan["fingerprint"],
            "cases": len(plan["cases"]), "solvers": plan["solvers"],
            "case_policy": plan["case_policy"], "jobs": len(plan["jobs"]),
            "selected_case_solver_pairs": len(plan["eligibility"]),
            "not_applicable": sum(not entry["eligible"] for entry in plan["eligibility"]),
            "eligibility_by_solver": {solver: sum(entry["eligible"] for entry in plan["eligibility"]
                                                   if entry["solver"] == solver) for solver in plan["solvers"]},
            "missing_inputs": sum(c["availability"] == "missing" for c in plan["cases"]),
            "runtime_command": plan["runtime_command"], "entrypoint": plan["entrypoint"],
            "timeout_seconds": plan["timeout_seconds"],
            "startup_grace_seconds": plan["startup_grace_seconds"],
            "runtime_tested": False,
            "fingerprint_is_provisional": True,
        }
        print(json.dumps(printable, indent=2, ensure_ascii=False))
        return 0
    if not plan["runtime_command"]:
        print("No Wolfram runtime found. Use doctor and set --wolfram-command; no solving was performed.", file=sys.stderr)
        return 2
    output_dir = Path(args.output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    lock_path = output_dir / ".runner.lock"
    try:
        descriptor = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        raise ValueError(f"run directory is locked: {lock_path}; inspect its PID before removing a stale lock")
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(json.dumps({"pid": os.getpid(), "started_at": event_stamp()}))
        plan_path = output_dir / "run_plan.json"
        results_path = output_dir / "results.jsonl"
        if plan_path.exists():
            previous = read_json(plan_path)
            if not args.resume:
                raise ValueError("run directory already has a plan; use --resume with identical inputs or a new directory")
            if previous.get("fingerprint") != plan["fingerprint"]:
                raise ValueError("resume refused: code, inputs, manifest, runtime, or configuration fingerprint changed")
            previous_payload = {k: v for k, v in previous.items() if k not in {"fingerprint", "created_at"}}
            if digest_object(previous_payload) != previous["fingerprint"]:
                raise ValueError("resume refused: saved run plan has been altered")
            plan = previous
        else:
            if results_path.exists() or (output_dir / "jobs").exists():
                raise ValueError("run directory contains records/jobs without a plan; use a new output directory")
            write_json(plan_path, plan)
        prior = read_results(results_path, plan["fingerprint"])
        eligibility = get_eligibility(plan)
        latest: dict[tuple[str, str], dict[str, Any]] = {}
        observed_claims: dict[str, set[str]] = {}
        case_map = {case["case_id"]: case for case in plan["cases"]}
        for record in prior:
            case_id, solver = record.get("case_id"), record.get("solver")
            if case_id not in case_map or solver not in plan["solvers"]:
                raise ValueError("resume refused: saved record references an unplanned case or solver")
            if not eligibility[(case_id, solver)]["eligible"]:
                raise ValueError("resume refused: saved record belongs to a not-applicable pair")
            case = case_map[case_id]
            for field in ("input_sha256", "expected_status", "benchmark", "family"):
                if record.get(field) != case.get(field):
                    raise ValueError(f"resume refused: saved record has mismatched {field}")
            if (record.get("configuration_sha256") != plan["configuration_sha256"]
                    or record.get("code_fingerprint") != digest_object(plan["code"])):
                raise ValueError("resume refused: saved record code/configuration digest differs")
            status = record.get("actual_status")
            if not isinstance(status, str) or status not in ACTUAL_STATUSES:
                raise ValueError("resume refused: saved record has an invalid result status")
            latest[(record["case_id"], record["solver"])] = record
            if status in {"sat", "unsat"}:
                observed_claims.setdefault(record["case_id"], set()).add(status)
        retry = set(filter(None, (s.strip() for s in args.retry_status.split(","))))
        if retry - {"unknown", "error", "timeout"}:
            raise ValueError("--retry-status only permits unknown,error,timeout")
        failures = 0
        with results_path.open("a", encoding="utf-8", newline="\n") as handle:
            for solver in plan["solvers"]:
                for case in plan["cases"]:
                    if not eligibility[(case["case_id"], solver)]["eligible"]:
                        continue
                    existing = latest.get((case["case_id"], solver))
                    if existing and existing.get("validation_conflict"):
                        print(f"VIOLATION already recorded: {case['case_id']} {solver}; inspect this run", file=sys.stderr)
                        return 1
                    if existing and existing.get("actual_status") not in retry:
                        continue
                    attempt = next_attempt(output_dir, plan["fingerprint"], case["case_id"], solver, existing)
                    record = execute_job(plan, case, solver, output_dir, attempt)
                    status = record["actual_status"]
                    prior_claims = observed_claims.setdefault(case["case_id"], set())
                    if status in {"sat", "unsat"}:
                        if prior_claims - {status}:
                            record.update(validation_conflict=True, effective_status="conflict",
                                          count_as_solved=False,
                                          failure_kind="contradictory_solver_claims",
                                          reason="SAT and UNSAT were reported for the same benchmark input")
                        prior_claims.add(status)
                    handle.write(json.dumps(record, ensure_ascii=False, allow_nan=False) + "\n")
                    handle.flush()
                    os.fsync(handle.fileno())
                    print(f"{case['case_id']} {solver}: {record['effective_status']}", flush=True)
                    if record["validation_conflict"]:
                        print(f"VIOLATION: {case['case_id']} {solver}: expected status={case['expected_status']}, "
                              f"actual={record['actual_status']}, observed claims={sorted(prior_claims)}; "
                              "this claim is NOT counted as solved.", file=sys.stderr)
                        return 1
                    if record["actual_status"] == "error":
                        failures += 1
        return 1 if failures else 0
    finally:
        lock_path.unlink(missing_ok=True)


def probe_runtime(args: argparse.Namespace) -> dict[str, Any]:
    prefix = runtime_prefix(args)
    report: dict[str, Any] = {"python_version": sys.version, "platform": sys.platform,
                              "runtime_command": prefix, "solver_verified": False,
                              "note": "Runtime availability does not validate the solver or experiment results."}
    if not prefix or not (Path(prefix[0]).is_file() or shutil.which(prefix[0])):
        report["runtime_status"] = "not_found"
        return report
    # Some installed launchers exit 0 without executing any WL expression. A
    # fresh, nonce-bound output file is proof that this particular script ran.
    ok = False
    with tempfile.TemporaryDirectory(prefix="helms-runtime-probe-") as temporary:
        directory = Path(temporary)
        script_path = directory / "doctor_probe.wls"
        proof_path = directory / "doctor_report.json"
        nonce = uuid.uuid4().hex
        wl_path = wolfram_string(proof_path.as_posix())
        wl_nonce = wolfram_string(nonce)
        script_path.write_text(
            f'Export[{wl_path}, <|"probe_nonce" -> {wl_nonce}, '
            '"wolfram_version" -> $Version, "system_id" -> $SystemID|>, "RawJSON"];\nExit[0];\n',
            encoding="utf-8")
        switch = "-file" if args.launch_mode == "file" else "-script"
        command = [*prefix, switch, str(script_path), *( ["--"] if args.launch_mode == "script" else [])]
        report["probe_command"] = command
        process = None
        try:
            options: dict[str, Any] = {"stdout": subprocess.PIPE, "stderr": subprocess.PIPE,
                                       "stdin": subprocess.DEVNULL}
            if os.name == "nt":
                options["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.CREATE_NO_WINDOW
            else:
                options["start_new_session"] = True
            process = subprocess.Popen(command, **options)
            stdout, stderr = process.communicate(timeout=args.probe_timeout)
            report.update(probe_exit_code=process.returncode,
                          probe_stdout=stdout.decode("utf-8", errors="replace")[-6000:],
                          probe_stderr=stderr.decode("utf-8", errors="replace")[-6000:])
            proof = read_json(proof_path) if proof_path.is_file() else None
            ok = (process.returncode == 0 and isinstance(proof, dict)
                  and proof.get("probe_nonce") == nonce
                  and isinstance(proof.get("wolfram_version"), str) and bool(proof["wolfram_version"])
                  and isinstance(proof.get("system_id"), str) and bool(proof["system_id"]))
            report["runtime_status"] = "available" if ok else "probe_failed"
            report["proof_of_execution"] = proof if ok else None
            if not ok:
                report["reason"] = "launcher did not produce valid nonce-bound proof of WL execution"
        except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
            if process is not None and process.poll() is None:
                terminate_process_tree(process)
            report.update(runtime_status="probe_failed", reason=str(exc), proof_of_execution=None)
    return report


def verified_runtime_identity(args: argparse.Namespace) -> dict[str, str]:
    report = probe_runtime(args)
    if report.get("runtime_status") != "available":
        raise ValueError("Wolfram preflight failed; actual script execution was not proved: "
                         + str(report.get("reason", report["runtime_status"])))
    proof = report["proof_of_execution"]
    return {"wolfram_version": proof["wolfram_version"], "system_id": proof["system_id"]}


def doctor(args: argparse.Namespace) -> int:
    report = probe_runtime(args)
    if args.report:
        write_json(Path(args.report).resolve(), report)
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0 if report["runtime_status"] == "available" else 2


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--wolfram-command", help="Executable name/path only; no shell command")
    common.add_argument("--runtime-args", default="[]", help="JSON array prepended before -file/-script")
    common.add_argument("--runtime-arg", action="append", default=[],
                        help="One runtime argument; repeat as needed, e.g. --runtime-arg=-noinit")
    common.add_argument("--launch-mode", choices=("file", "script"), default="file")
    common.add_argument("--probe-timeout", type=float, default=30)
    diagnosis = commands.add_parser("doctor", parents=[common], help="Probe the actual runtime; never claims solver validation")
    diagnosis.add_argument("--report", help="Save the UTF-8 JSON runtime probe report")
    experiment = commands.add_parser("run", parents=[common])
    experiment.add_argument("--manifest", required=True)
    experiment.add_argument("--output-dir", required=True)
    experiment.add_argument("--config")
    experiment.add_argument("--entrypoint", default=str(PACKAGE_ROOT / "components" / "entrypoint.wls"))
    experiment.add_argument("--code", action="append", default=[], help="Additional code file/directory to fingerprint")
    experiment.add_argument("--solvers", default=",".join(DEFAULT_SOLVERS))
    experiment.add_argument("--case-policy", choices=("paper", "all"), default="paper",
                            help="paper: confirmed SAT for 2D-LS/LS-WL/1D-control, confirmed SAT+UNSAT for others; all: every available case")
    experiment.add_argument("--seed", type=int, default=314159)
    experiment.add_argument("--timeout", type=float, default=1200)
    experiment.add_argument("--startup-grace", type=float, default=60)
    experiment.add_argument("--case-id", action="append", default=[])
    experiment.add_argument("--benchmark", action="append", default=[])
    experiment.add_argument("--max-cases", type=int)
    experiment.add_argument("--dry-run", action="store_true")
    experiment.add_argument("--resume", action="store_true")
    experiment.add_argument("--retry-status", default="", help="Explicitly retry previous unknown,error,timeout records")
    return result


def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(errors="backslashreplace")
    args = parser().parse_args(argv)
    try:
        return doctor(args) if args.command == "doctor" else run(args)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
