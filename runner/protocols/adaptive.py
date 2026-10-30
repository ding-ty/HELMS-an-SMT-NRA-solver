#!/usr/bin/env python3
"""Two-machine, bounded-memory, single-CPU experiment scheduler.

Solver/entrypoint files remain unchanged. Every fresh attempt receives the full
solve timeout. Aborted attempts remain in the audit journal without consuming
the next attempt's timeout or the final solver-time measurement.
"""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
from contextlib import contextmanager
from dataclasses import dataclass
import json
import math
import os
import platform
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from typing import Any

try:
    from . import core as serial
    from .plan import attach_parallel_plan, assigned_jobs, validate_local_campaign
    from .resources import LinuxResources, ResourceConfig, ResourceError
    from .adaptive_windows import WindowsResources
except ImportError:
    import core as serial
    from plan import attach_parallel_plan, assigned_jobs, validate_local_campaign
    from resources import LinuxResources, ResourceConfig, ResourceError
    from adaptive_windows import WindowsResources

ROOT = Path(__file__).resolve().parents[2]


@contextmanager
def interrupt_safe_section():
    """Defer Ctrl+C/TERM until launch registration or journal commit completes.

    Handler deferral avoids inheriting a blocked POSIX signal mask in children.
    It does not pause a worker or change a worker's solve-time accounting.
    """
    pending = []
    signals = [signal.SIGINT]
    if hasattr(signal, "SIGTERM"):
        signals.append(signal.SIGTERM)
    previous = {number: signal.getsignal(number) for number in signals}

    def defer(number, _frame):
        pending.append(number)

    try:
        for number in signals:
            signal.signal(number, defer)
        yield
    finally:
        for number, handler in previous.items():
            signal.signal(number, handler)
        if pending:
            raise KeyboardInterrupt


def append_json(path: Path, record: dict[str, Any]) -> None:
    with path.open("a", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(record, ensure_ascii=False, allow_nan=False) + "\n")
        stream.flush()
        os.fsync(stream.fileno())


def resource_config(args: argparse.Namespace) -> ResourceConfig:
    return ResourceConfig(max_workers=args.workers,
                          reserve_ram_gib=args.reserve_ram_gib,
                          reserve_swap_gib=args.reserve_swap_gib,
                          minimum_worker_gib=args.minimum_worker_gib,
                          pressure_available_gib=args.pressure_available_gib,
                          cgroup_parent=args.cgroup_parent,
                          poll_seconds=args.poll_seconds,
                          commit_budget_gib=args.commit_budget_gib,
                          reserve_commit_gib=args.reserve_commit_gib)


def make_resources(config, run_id):
    return WindowsResources(config, run_id) if os.name == "nt" else LinuxResources(config, run_id)


def portable_policy(config: ResourceConfig, description: dict[str, Any] | None,
                    args: argparse.Namespace) -> dict[str, Any]:
    policy = {
        "revision": "adaptive-cgroup-v3", "max_workers": config.max_workers,
        "reserve_ram_gib": config.reserve_ram_gib,
        "reserve_swap_gib": config.reserve_swap_gib,
        "minimum_worker_gib": config.minimum_worker_gib,
        "pressure_available_gib": config.pressure_available_gib,
        "pressure_fraction": config.pressure_fraction,
        "poll_seconds": config.poll_seconds,
        "max_resource_retries": args.max_resource_retries,
        "cpu_policy": "one-logical-cpu-per-distinct-linux-reported-core",
        "thread_environment_limit": 1,
        "memory_policy": "shared-parent-hard-limit-adaptive-child-high-exclusive-resource-retry",
        "time_accounting": "per_attempt_full_budget_final_solve",
        "pause_workers": False,
        "event_time_policy": "opaque-session-relative-elapsed-no-calendar-v1",
        "execution_order": "solver-major-local-drain-barrier-v1",
    }
    if description:
        if description.get("backend") == "windows-job-objects":
            policy.update(revision="adaptive-windows-job-v3",
                          cpu_policy="windows-nested-job-single-cpu-per-physical-core",
                          memory_policy="shared-job-private-commit-hard-limit-dynamic-notifications-exclusive-retry")
            policy.pop("reserve_swap_gib", None)
            policy["resource_ceiling"] = {
                "commit_budget_bytes": description["commit_budget_bytes"],
                "reserve_commit_gib": config.reserve_commit_gib,
                "ram_soft_budget_bytes": description["ram_budget_bytes"],
                "windows_version": description["kernel"],
                "cpu_models": description["cpu_models"],
                "worker_cpus": len(description["cpus"]),
                "cpu_limit_backend": description["cpu_limit_backend"],
            }
            return policy
        policy["resource_ceiling"] = {
            "ram_budget_bytes": description["ram_budget_bytes"],
            "swap_budget_bytes": description["swap_budget_bytes"],
            "linux_kernel": description["kernel"],
            "worker_cpus": len(description["cpus"]),
        }
        models = sorted({line.split(":", 1)[1].strip() for line in
                         Path("/proc/cpuinfo").read_text().splitlines()
                         if line.startswith("model name")})
        policy["resource_ceiling"]["cpu_models"] = models
    else:
        policy["resource_ceiling"] = "PROVISIONAL: doctor has not verified native resource limits"
    return policy


def runtime_plan(args: argparse.Namespace, identity: dict[str, str] | None,
                 policy: dict[str, Any]) -> dict[str, Any]:
    # Build through the original input/code/config validators without launching
    # an unprotected probe; the protected four-kernel doctor supplies identity.
    values = vars(args).copy()
    values.update(dry_run=True, runtime_arg=[], code=[], case_policy=args.case_policy,
                  max_cases=None, entrypoint=str(ROOT / "components/entrypoint.wls"))
    base = serial.make_plan(argparse.Namespace(**values))
    base["runtime_identity"] = identity
    return attach_parallel_plan(base, policy, args.shard_index, args.shards, ROOT)


def four_kernel_probe(args: argparse.Namespace, resources: LinuxResources,
                      directory: Path) -> dict[str, str]:
    """Nonce-bound probes remain alive together until all four report ready."""
    prefix = serial.runtime_prefix(args)
    if not prefix:
        raise ResourceError("No Mathematica command-line kernel found")
    directory.mkdir(parents=True, exist_ok=True)
    gate = directory / "release_gate"
    nonce = uuid.uuid4().hex
    proofs = []
    streams = []
    try:
        for slot in range(args.workers):
            proof = directory / f"kernel-{slot}.json"
            script = directory / f"kernel-{slot}.wls"
            script.write_text(
                'proof = <|"nonce" -> ' + serial.wolfram_string(nonce) +
                ', "wolfram_version" -> $Version, "system_id" -> $SystemID, "pid" -> $ProcessID|>;\n'
                'Export[' + serial.wolfram_string(str(proof)) + ', proof, "RawJSON"];\n'
                'While[!FileExistsQ[' + serial.wolfram_string(str(gate)) + '], Pause[0.1]];\nExit[0];\n',
                encoding="utf-8")
            out = (directory / f"kernel-{slot}.stdout.log").open("wb")
            err = (directory / f"kernel-{slot}.stderr.log").open("wb")
            streams.extend([out, err])
            switch = "-script" if args.launch_mode == "script" else "-file"
            resources.spawn([*prefix, switch, str(script)], cwd=ROOT,
                            env=os.environ, slot=slot, stdout=out, stderr=err)
            proofs.append(proof)
        deadline = time.monotonic() + args.probe_timeout
        while time.monotonic() < deadline:
            if any(item.process.poll() is not None for item in resources.managed.values()):
                raise ResourceError("A simultaneous license probe exited before all kernels were ready; inspect preflight logs")
            try:
                data = [serial.read_json(path) for path in proofs]
            except (OSError, ValueError):
                time.sleep(.1)
                continue
            if all(isinstance(row, dict) and row.get("nonce") == nonce for row in data):
                if len({row.get("pid") for row in data}) != args.workers:
                    raise ResourceError("License probes did not use distinct fresh kernel PIDs")
                if hasattr(resources, "contains_pid"):
                    for slot, row in enumerate(data):
                        if not resources.contains_pid(slot, row["pid"]):
                            raise ResourceError("Mathematica kernel escaped its protected Windows Job Object")
                identities = [{"wolfram_version": row.get("wolfram_version"),
                               "system_id": row.get("system_id")} for row in data]
                if not all(identity == identities[0] for identity in identities):
                    raise ResourceError("Simultaneous kernels reported different Mathematica versions")
                if not all(isinstance(v, str) and v for v in identities[0].values()):
                    raise ResourceError("License probe did not report a valid Wolfram runtime identity")
                serial.write_json(directory / "simultaneous_kernel_proof.json",
                                  {"concurrent_kernels_verified": args.workers, "proofs": data})
                gate.write_text("release", encoding="ascii")
                for slot in list(resources.managed):
                    item = resources.managed[slot]
                    item.process.wait(timeout=15)
                    if item.process.returncode:
                        raise ResourceError("License probe did not exit successfully")
                    resources.finish(slot)
                return identities[0]
        raise ResourceError(f"All {args.workers} Mathematica kernels did not become ready within {args.probe_timeout}s; verify license concurrency and logs")
    finally:
        gate.touch()
        for slot in list(resources.managed):
            resources.kill(slot)
            resources.finish(slot)
        for stream in streams:
            stream.close()


@dataclass
class Active:
    job: dict[str, Any]
    record: dict[str, Any]
    result_path: Path
    job_dir: Path
    slot: int
    started: float
    budget: float
    prior_wall: float
    exclusive: bool
    streams: tuple[Any, Any]


def prior_cost(attempts: list[dict[str, Any]]) -> float:
    return sum(float(row["worker_wall_seconds"]) for row in attempts)


def resource_failures(attempts: list[dict[str, Any]]) -> int:
    return sum(bool(row.get("resource_aborted")) for row in attempts)


def prepare_attempt(plan: dict[str, Any], job: dict[str, Any], output: Path,
                    attempts: list[dict[str, Any]], slot: int, exclusive: bool,
                    resources: LinuxResources) -> Active:
    cases = {case["case_id"]: case for case in plan["cases"]}
    case, solver = cases[job["case_id"]], job["solver"]
    fingerprint = plan["fingerprint"]
    job_key = serial.digest_object({"fingerprint": fingerprint,
                                   "case_id": case["case_id"], "solver": solver})
    previous = attempts[-1] if attempts else None
    attempt = serial.next_attempt(output, fingerprint, case["case_id"], solver, previous)
    job_dir = output / "jobs" / job_key[:24] / f"attempt-{attempt:04d}"
    job_dir.mkdir(parents=True, exist_ok=False)
    request_path = job_dir / "request.json"
    result_path = job_dir / "worker_result.json"
    out_path, err_path = job_dir / "stdout.log", job_dir / "stderr.log"
    prior_wall = prior_cost(attempts)
    budget = plan["timeout_seconds"]
    if not serial.finite_nonnegative(budget) or budget <= 0:
        raise ValueError("Each attempt requires a finite positive full solve timeout")
    record = {
        "schema_version": 1, "fingerprint": fingerprint, "job_key": job_key,
        "attempt": attempt, "case_id": case["case_id"], "solver": solver,
        "benchmark": case["benchmark"], "family": case["family"],
        "expected_status": case["expected_status"], "input_path": case["input_path"],
        "input_sha256": case["input_sha256"], "seed": plan["seed"],
        "timeout_seconds": plan["timeout_seconds"], "configuration_sha256": plan["configuration_sha256"],
        "code_fingerprint": serial.digest_object(plan["code"]),
        "runtime_identity": plan["runtime_identity"], "case_policy": plan["case_policy"],
        "started_at": serial.event_stamp(), "request_path": str(request_path),
        "worker_result_path": str(result_path), "stdout_log": str(out_path), "stderr_log": str(err_path),
        "campaign_fingerprint": plan["parallel"]["campaign"]["fingerprint"],
        "campaign_job_key": job["campaign_job_key"], "global_job_index": job["global_job_index"],
        "shard_index": job["shard_index"], "slot": slot,
        "exclusive_resource_retry": exclusive, "attempt_timeout_seconds": budget,
        "charged_prior_wall_seconds": 0.0,
        "prior_attempt_wall_seconds": prior_wall,
        "resource_policy_sha256": serial.digest_object(plan["parallel"]["resource_policy"]),
        "timing_basis": "per_attempt_full_budget_final_solve",
    }
    request = {
        "schema_version": 1, "fingerprint": fingerprint, "case_id": case["case_id"],
        "input_path": case["input_path"], "input_sha256": case["input_sha256"],
        "solver": solver, "seed": plan["seed"], "timeout_seconds": budget,
        "worker_result_path": str(result_path),
        "worker_config": plan["configuration"].get("worker", plan["configuration"]),
        "package_root": str(ROOT), "code": plan["code"],
    }
    serial.write_json(request_path, request)
    serial.write_json(job_dir / "attempt_state.json", {"state": "starting", "record": record})
    streams = (out_path.open("wb"), err_path.open("wb"))
    command = serial.worker_command(plan, request_path)
    record["command"] = command
    started = time.monotonic()
    try:
        process = resources.spawn(command, cwd=ROOT, env=os.environ, slot=slot,
                                  stdout=streams[0], stderr=streams[1])
    except BaseException:
        for stream in streams:
            stream.close()
        # Orphan markers require review before retry, so attempts never vanish.
        raise
    record["worker_pid"] = process.process.pid
    record["cpu_affinity"] = [process.cpu]
    record["cgroup"] = str(process.cgroup)
    serial.write_json(job_dir / "attempt_state.json", {"state": "running", "record": record})
    return Active(job, record, result_path, job_dir, slot, started, budget, prior_wall, exclusive, streams)


def finish_attempt(active: Active, resources: LinuxResources,
                   reason: str | None = None) -> dict[str, Any]:
    item = resources.managed[active.slot]
    usage = resources.usage(active.slot)
    if reason is not None or item.process.poll() is None:
        resources.kill(active.slot)
    exit_code = item.process.wait()
    usage_after = resources.finish(active.slot)
    if usage_after.memory_peak >= usage.memory_peak:
        usage = usage_after
    for stream in active.streams:
        stream.close()
    elapsed = time.monotonic() - active.started
    resource_abort = reason == "memory_pressure" or usage.oom_killed
    if resource_abort:
        result = {"actual_status": "error", "failure_kind": "resource_exhausted" if active.exclusive else "resource_pressure",
                  "reason": "exclusive attempt exhausted the protected machine resource budget" if active.exclusive else "protected memory limit or memory pressure; eligible for an exclusive retry with a fresh full timeout"}
    elif reason == "interrupted":
        result = {"actual_status": "error", "failure_kind": "interrupted", "reason": "user interrupted this attempt; it is retained for audit and resume receives the full solve timeout"}
    elif reason == "wall_timeout":
        result = {"actual_status": "timeout", "failure_kind": "process_wall_timeout",
                  "reason": "full per-attempt solve timeout plus startup grace exceeded"}
    elif exit_code != 0:
        result = {"actual_status": "error", "failure_kind": "worker_exit", "reason": f"worker exited with code {exit_code}"}
    elif not active.result_path.is_file():
        result = {"actual_status": "error", "failure_kind": "missing_worker_result", "reason": "worker exited without a result"}
    else:
        try:
            result = serial.normalize_worker_result(serial.read_json(active.result_path), active.budget)
        except (OSError, ValueError) as exc:
            result = {"actual_status": "error", "failure_kind": "invalid_worker_result", "reason": str(exc)}
    record = dict(active.record)
    metadata = result.get("solver_metadata")
    if result["actual_status"] in {"sat", "unsat"}:
        if not isinstance(metadata, dict) or any(metadata.get(k) != v for k, v in record["runtime_identity"].items()):
            result = {**result, "actual_status": "error", "failure_kind": "runtime_identity_mismatch", "reason": "worker runtime differs from preflight"}
        elif result["actual_status"] == "sat" and metadata.get("model_verified") is not True:
            result = {**result, "actual_status": "error", "failure_kind": "unverified_sat_model", "reason": "SAT lacks exact worker model verification"}
    record["worker_result"] = result
    for key in ("actual_status", "solve_seconds", "startup_seconds", "stage", "reason", "failure_kind", "reported_status", "solver_metadata"):
        if key in result:
            record[key] = result[key]
    record.update(worker_exit_code=exit_code, worker_wall_seconds=elapsed,
                  finished_at=serial.event_stamp(), resource_aborted=resource_abort,
                  resource_usage=usage.to_dict(), final_attempt_solve_seconds=result.get("solve_seconds"))
    # Only the final attempt's solver time is measured for the comparison.
    # Earlier attempts remain in the journal with their recorded durations.
    conflict = (record["actual_status"] in {"sat", "unsat"} and
                record["expected_status"] in {"sat", "unsat"} and
                record["actual_status"] != record["expected_status"])
    record.update(validation_conflict=conflict,
                  effective_status="conflict" if conflict else record["actual_status"],
                  count_as_solved=record["actual_status"] in {"sat", "unsat"} and not conflict)
    serial.write_json(active.job_dir / "attempt_state.json", {"state": "finished", "record": record})
    return record


def finalized(record: dict[str, Any], previous: list[dict[str, Any]]) -> dict[str, Any]:
    result = dict(record)
    result["resource_retry_count"] = resource_failures(previous)
    result["all_attempt_wall_seconds"] = prior_cost(previous) + record["worker_wall_seconds"]
    result["attempts_journal"] = "attempts.jsonl"
    return result


def restore(output: Path, plan: dict[str, Any], jobs: list[dict[str, Any]]) -> tuple[dict, dict]:
    allowed = {(job["case_id"], job["solver"]): job for job in jobs}
    history = defaultdict(list)
    for record in serial.read_results(output / "attempts.jsonl", plan["fingerprint"]):
        key = (record.get("case_id"), record.get("solver"))
        if key not in allowed or record.get("campaign_job_key") != allowed[key]["campaign_job_key"]:
            raise ValueError("Attempt journal contains a job outside this shard")
        if not serial.finite_nonnegative(record.get("worker_wall_seconds")):
            raise ValueError("Attempt journal is missing audited wall time")
        if history[key] and history[key][-1]["attempt"] >= record["attempt"]:
            raise ValueError("Attempt journal is duplicated or out of order")
        history[key].append(record)
    # Recover only finished, atomically committed states after a narrow crash
    # between state.json and journal fsync. Running/orphaned states need review.
    known = {(r["job_key"], r["attempt"]) for rows in history.values() for r in rows}
    recovered = []
    for state_path in output.glob("jobs/*/attempt-*/attempt_state.json"):
        state = serial.read_json(state_path)
        record = state["record"]
        identity = (record["job_key"], record["attempt"])
        if identity in known:
            continue
        if state.get("state") != "finished":
            raise ValueError("An unfinalized attempt survived a crash; preserve this run and inspect " + str(state_path) + "; refusing to discard an unaudited attempt")
        key = (record["case_id"], record["solver"])
        if key not in allowed or record.get("fingerprint") != plan["fingerprint"]:
            raise ValueError("Orphan attempt does not belong to this campaign")
        recovered.append(record)
    for record in sorted(recovered, key=lambda r: r["attempt"]):
        key = (record["case_id"], record["solver"])
        if history[key] and history[key][-1]["attempt"] >= record["attempt"]:
            raise ValueError("Recovered attempt order is inconsistent")
        append_json(output / "attempts.jsonl", record)
        history[key].append(record)
    final = {}
    for record in serial.read_results(output / "results.jsonl", plan["fingerprint"]):
        key = (record.get("case_id"), record.get("solver"))
        if key not in allowed or key in final:
            raise ValueError("Final results contain an unplanned or duplicate job")
        if not history[key] or history[key][-1]["attempt"] != record["attempt"]:
            raise ValueError("Final result does not have its completed attempt journal")
        final[key] = record
    return history, final


def schedule(plan: dict[str, Any], output: Path, resources: LinuxResources,
             args: argparse.Namespace) -> int:
    jobs = assigned_jobs(plan)
    history, final = restore(output, plan, jobs)
    solver_order = list(plan.get("solvers", dict.fromkeys(job["solver"] for job in jobs)))
    if len(set(solver_order)) != len(solver_order) or any(job["solver"] not in solver_order for job in jobs):
        raise ValueError("Invalid solver batch order")
    normal_by_solver = {solver: deque() for solver in solver_order}
    exclusive_by_solver = {solver: deque() for solver in solver_order}
    for job in jobs:
        key = (job["case_id"], job["solver"])
        if key in final:
            if final[key].get("validation_conflict"):
                raise ValueError("Previous conflicting result must be inspected")
            continue
        rows = history[key]
        if rows and not rows[-1].get("resource_aborted") and rows[-1].get("failure_kind") != "interrupted":
            record = finalized(rows[-1], rows[:-1])
            append_json(output / "results.jsonl", record)
            final[key] = record
            continue
        if rows and rows[-1].get("resource_aborted") and (rows[-1].get("exclusive_resource_retry") or resource_failures(rows) > args.max_resource_retries):
            record = finalized(rows[-1], rows[:-1])
            record.update(actual_status="error", effective_status="error", count_as_solved=False,
                          failure_kind="resource_exhausted", reason="resource retry allowance exhausted")
            append_json(output / "results.jsonl", record)
            final[key] = record
            continue
        (exclusive_by_solver if resource_failures(rows) else normal_by_solver)[job["solver"]].append(job)
    remaining_solvers = deque(solver_order)
    queue, exclusive_queue = deque(), deque()
    current_solver = None
    active: dict[int, Active] = {}
    last_sample = 0.0
    stop = False

    def _complete(slot: int, reason: str | None = None):
        nonlocal stop
        task = active.pop(slot)
        key = (task.job["case_id"], task.job["solver"])
        previous = list(history[key])
        record = finish_attempt(task, resources, reason)
        append_json(output / "attempts.jsonl", record)
        history[key].append(record)
        if reason == "interrupted":
            return
        retry = (record["resource_aborted"] and not task.exclusive
                 and resource_failures(previous) < args.max_resource_retries)
        if retry:
            exclusive_queue.append(task.job)
            print(f"RESOURCE RETRY QUEUED {task.job['case_id']} {task.job['solver']}; previous {record['worker_wall_seconds']:.2f}s audit only; retry gets full {plan['timeout_seconds']:g}s", flush=True)
            return
        result = finalized(record, previous)
        append_json(output / "results.jsonl", result)
        final[key] = result
        stop = stop or result["validation_conflict"]
        print(f"[{len(final)}/{len(jobs)}] {task.job['case_id']} {task.job['solver']}: {result['effective_status']}", flush=True)

    def complete(slot: int, reason: str | None = None):
        with interrupt_safe_section():
            _complete(slot, reason)

    try:
        while current_solver is not None or active or queue or exclusive_queue or remaining_solvers:
            # Advancing requires all ordinary work, exclusive retries and live
            # workers of this solver to have drained. Future retries stay in
            # their own solver's bucket, including when resuming a stopped run.
            if not active and not queue and not exclusive_queue:
                if resources.managed:
                    raise ResourceError("Cannot change solver while protected worker processes remain")
                if current_solver is not None:
                    append_json(output / "scheduler_events.jsonl", {
                        "at": serial.event_stamp(), "event": "solver_finished", "solver": current_solver,
                        "completed_jobs": sum(row["solver"] == current_solver for row in final.values())})
                    print(f"SOLVER END {current_solver}; all local tasks and retries finished", flush=True)
                current_solver = None
                while remaining_solvers:
                    solver = remaining_solvers.popleft()
                    if normal_by_solver[solver] or exclusive_by_solver[solver]:
                        current_solver = solver
                        queue = normal_by_solver[solver]
                        exclusive_queue = exclusive_by_solver[solver]
                        append_json(output / "scheduler_events.jsonl", {
                            "at": serial.event_stamp(), "event": "solver_started", "solver": solver,
                            "pending_jobs": len(queue) + len(exclusive_queue)})
                        print(f"SOLVER BEGIN {solver}; {len(queue) + len(exclusive_queue)} local jobs pending", flush=True)
                        break
                    print(f"SOLVER SKIP {solver}; all local jobs already completed", flush=True)
                if current_solver is None:
                    break
            # Retire dead kernels before considering pressure; never sacrifice a
            # healthy worker because a dead cgroup still appears in a sample.
            for slot in list(active):
                task = active[slot]
                if resources.usage(slot).oom_killed:
                    complete(slot, "memory_pressure")
                elif resources.managed[slot].process.poll() is not None:
                    complete(slot)
                elif time.monotonic() - task.started >= task.budget + plan["startup_grace_seconds"]:
                    complete(slot, "wall_timeout")
            if stop:
                break
            sample = resources.rebalance()
            now = time.monotonic()
            if now - last_sample >= 5:
                append_json(output / "resource_metrics.jsonl", {"at": serial.event_stamp(), **sample.to_dict()})
                last_sample = now
            should_abort = (len(active) > 1 or any(reason != "sustained_memory_stall" for reason in sample.reasons))
            if sample.pressure and sample.victim_slot in active and should_abort:
                victim = sample.victim_slot
                append_json(output / "scheduler_events.jsonl", {"at": serial.event_stamp(), "event": "resource_abort", "slot": victim, "reasons": sample.reasons})
                complete(victim, "memory_pressure")
                continue
            if not active and exclusive_queue:
                job = exclusive_queue.popleft()
                key = (job["case_id"], job["solver"])
                if sample.admit_new:
                    with interrupt_safe_section():
                        active[0] = prepare_attempt(plan, job, output, history[key], 0, True, resources)
                    print(f"EXCLUSIVE {job['case_id']} {job['solver']}; full solve timeout {plan['timeout_seconds']:g}s", flush=True)
                else:
                    exclusive_queue.appendleft(job)
            elif not exclusive_queue and not any(task.exclusive for task in active.values()) and queue and sample.admit_new:
                # One launch per control tick lets the monitor see startup RSS
                # before admitting the next kernel.
                slot = next(i for i in range(args.workers) if i not in active)
                job = queue.popleft()
                key = (job["case_id"], job["solver"])
                with interrupt_safe_section():
                    active[slot] = prepare_attempt(plan, job, output, history[key], slot, False, resources)
                print(f"START slot={slot} cpu={resources.managed[slot].cpu} {job['case_id']} {job['solver']}", flush=True)
            if not active and (queue or exclusive_queue) and not sample.admit_new:
                raise ResourceError("No safe memory headroom to start even one worker; stop other programs and resume this unchanged run")
            time.sleep(args.poll_seconds)
    finally:
        for slot in list(active):
            complete(slot, "interrupted")
    append_json(output / "scheduler_events.jsonl", {"at": serial.event_stamp(), "event": "shard_stopped", "recorded": len(final), "assigned": len(jobs)})
    return 1 if stop or any(row["actual_status"] == "error" for row in final.values()) else 0


def run(args: argparse.Namespace) -> int:
    config = resource_config(args)
    if args.dry_run:
        plan = runtime_plan(args, None, portable_policy(config, None, args))
        jobs = assigned_jobs(plan)
        print(json.dumps({"provisional": True, "total_jobs": len(plan["jobs"]),
                          "assigned_jobs": len(jobs), "shard_index": args.shard_index,
                          "solvers": plan["solvers"], "max_workers": args.workers,
                          "execution_order": plan["parallel"]["resource_policy"]["execution_order"],
                          "benchmarks": sorted({case["benchmark"] for case in plan["cases"]}),
                          "case_policy": "paper", "note": "Dry run does not verify native resource limits or four-kernel license."}, indent=2))
        return 0
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    lock = output / ".runner.lock"
    descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    resources = make_resources(config, uuid.uuid4().hex)
    try:
        with os.fdopen(descriptor, "w") as stream:
            json.dump({"pid": os.getpid(), "started_at": serial.event_stamp(), "parallel": True}, stream)
        if (output / "run_plan.json").exists() and not args.resume:
            raise ValueError("Output already has a plan. Use identical settings with --resume or a new directory")
        description = resources.prepare()
        preflight_dir = output / "preflight" / uuid.uuid4().hex
        serial.write_json(preflight_dir / "resources.json", description)
        identity = four_kernel_probe(args, resources, preflight_dir)
        policy = portable_policy(config, description, args)
        plan = runtime_plan(args, identity, policy)
        if (output / "run_plan.json").exists():
            previous = serial.read_json(output / "run_plan.json")
            validate_local_campaign(previous)
            if previous["fingerprint"] != plan["fingerprint"]:
                raise ValueError("Resume refused: code, inputs, runtime, resource policy or shard changed")
            plan = previous
        else:
            if (output / "results.jsonl").exists() or (output / "jobs").exists() or (output / "attempts.jsonl").exists():
                raise ValueError("Records without a matching plan exist; preserve them and choose a new directory")
            serial.write_json(output / "run_plan.json", plan)
        # An empty filtered shard still has valid, summarizable raw files.
        (output / "results.jsonl").touch(exist_ok=True)
        (output / "attempts.jsonl").touch(exist_ok=True)
        environment = {"at": serial.event_stamp(), "resources": description,
                       "runtime_identity": identity, "python": sys.version,
                       "campaign_fingerprint": plan["parallel"]["campaign"]["fingerprint"]}
        serial.write_json(preflight_dir / "environment.json", environment)
        serial.write_json(output / "environment_latest.json", environment)
        print(f"Campaign {plan['parallel']['campaign']['fingerprint']} shard {args.shard_index}/{args.shards}: {len(assigned_jobs(plan))} jobs, up to {args.workers} single-CPU kernels", flush=True)
        if args.plan_only:
            message = ("Plan and environment saved; no benchmark jobs started. Repeat this single-machine command with --resume."
                       if args.shards == 1 else
                       "Plan and environment saved; no benchmark jobs started. Compare the campaign fingerprint on both machines, then repeat with --resume.")
            print(message, flush=True)
            return 0
        code = schedule(plan, output, resources, args)
    finally:
        resources.close()
        lock.unlink(missing_ok=True)
    # A one-shard campaign has every job here and needs no merge. In a
    # multi-shard campaign the other machines' jobs remain not_run locally.
    summarize_command = [sys.executable, str(Path(__file__).with_name("summary.py")),
                         "--results", str(output / "results.jsonl"), "--output-dir", str(output / "summary")]
    summary_code = subprocess.run(summarize_command, check=False).returncode
    return max(code, summary_code)


def doctor(args: argparse.Namespace) -> int:
    resources = make_resources(resource_config(args), uuid.uuid4().hex)
    report: dict[str, Any] = {"checked_at": serial.event_stamp(), "ok": False, "python_version": sys.version}
    try:
        description = resources.prepare()
        report["resources"] = description
        if args.report:
            probe_dir = args.report.resolve().parent / (args.report.stem + "_probes_" + uuid.uuid4().hex)
            identity = four_kernel_probe(args, resources, probe_dir)
        else:
            with tempfile.TemporaryDirectory(prefix="helms-parallel-doctor-") as temporary:
                identity = four_kernel_probe(args, resources, Path(temporary))
        report.update(ok=True, resources=description, runtime_identity=identity,
                      concurrent_kernels_verified=args.workers)
    except (ValueError, OSError, ResourceError, subprocess.SubprocessError) as exc:
        report["error"] = str(exc)
    finally:
        resources.close()
    if args.report:
        serial.write_json(args.report, report)
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if report["ok"] else 2


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--wolfram-command", default=None, help="Native Windows math.exe/WolframKernel.exe; resolved from PATH or passed by PowerShell helpers")
    common.add_argument("--runtime-args", default='["-noinit"]')
    common.add_argument("--launch-mode", choices=("script", "file"), default="script")
    common.add_argument("--workers", type=int, default=4)
    common.add_argument("--reserve-ram-gib", type=float, default=2.0)
    common.add_argument("--reserve-swap-gib", type=float, default=1.0)
    common.add_argument("--commit-budget-gib", type=float, default=32.0, help="Windows whole-batch private committed memory cap, not physical RAM")
    common.add_argument("--reserve-commit-gib", type=float, default=4.0)
    common.add_argument("--minimum-worker-gib", type=float, default=.75)
    common.add_argument("--pressure-available-gib", type=float, default=.75)
    common.add_argument("--cgroup-parent", default="/sys/fs/cgroup")
    common.add_argument("--poll-seconds", type=float, default=.5)
    common.add_argument("--probe-timeout", type=float, default=90)
    common.set_defaults(runtime_arg=[])
    diagnosis = sub.add_parser("doctor", parents=[common])
    diagnosis.add_argument("--report", type=Path)
    experiment = sub.add_parser("run", parents=[common])
    experiment.add_argument("--manifest", type=Path, default=ROOT / "benchmarks/experiment_default.jsonl")
    experiment.add_argument("--config", type=Path, default=ROOT / "config/run_config.json")
    experiment.add_argument("--solvers", default=",".join(serial.DEFAULT_SOLVERS))
    experiment.add_argument("--shards", type=int, default=2)
    experiment.add_argument("--shard-index", type=int, required=True)
    experiment.add_argument("--output-dir", type=Path, required=True)
    experiment.add_argument("--timeout", type=float, default=60)
    experiment.add_argument("--case-policy", choices=("paper", "all"), default="paper")
    experiment.add_argument("--startup-grace", type=float, default=60)
    experiment.add_argument("--seed", type=int, default=314159)
    experiment.add_argument("--max-resource-retries", type=int, default=1)
    experiment.add_argument("--benchmark", action="append", default=[])
    experiment.add_argument("--case-id", action="append", default=[])
    experiment.add_argument("--resume", action="store_true")
    experiment.add_argument("--dry-run", action="store_true")
    experiment.add_argument("--plan-only", action="store_true", help="Verify resources/license and save the campaign without benchmark solving; actual run then uses --resume")
    return result


def main(argv=None) -> int:
    args = parser().parse_args(argv)
    if not math.isfinite(args.poll_seconds) or args.poll_seconds <= 0:
        raise SystemExit("--poll-seconds must be finite and positive")
    if args.command == "run" and (not math.isfinite(args.timeout) or args.timeout <= 0):
        raise SystemExit("--timeout must be finite and positive")
    if args.command == "run" and args.max_resource_retries < 0:
        raise SystemExit("--max-resource-retries must be nonnegative")

    def interrupted(_signum, _frame):
        raise KeyboardInterrupt

    if hasattr(signal, "SIGTERM"):
        signal.signal(signal.SIGTERM, interrupted)
    try:
        return doctor(args) if args.command == "doctor" else run(args)
    except KeyboardInterrupt:
        print("Stopped. Completed records and interrupted attempts are retained. Resume gives each unfinished job a fresh full timeout; use identical arguments and --resume.", file=sys.stderr)
        return 130
    except (ValueError, OSError, ResourceError, subprocess.SubprocessError) as exc:
        print("ERROR: " + str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
