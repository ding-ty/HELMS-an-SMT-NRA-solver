#!/usr/bin/env python3
"""Derive checked tables from one immutable run plan and its JSONL records."""
from __future__ import annotations

import argparse
import collections
import csv
import json
import math
from pathlib import Path
import sys
from typing import Any

try:
    from .core import ACTUAL_STATUSES, digest_object, get_eligibility, read_json, sha256_file, write_json
except ImportError:
    from core import ACTUAL_STATUSES, digest_object, get_eligibility, read_json, sha256_file, write_json


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def valid_seconds(value: Any) -> bool:
    return (isinstance(value, (int, float)) and not isinstance(value, bool)
            and math.isfinite(value) and value >= 0)


def attempt_timing_error(record: dict[str, Any], budget: float) -> str | None:
    """Check final-attempt measurement without charging abandoned attempts."""
    if record.get("timing_basis") != "per_attempt_full_budget_final_solve":
        return "record does not use the plan's full per-attempt timing policy"
    attempt_budget = record.get("attempt_timeout_seconds")
    charged = record.get("charged_prior_wall_seconds")
    prior = record.get("prior_attempt_wall_seconds")
    wall = record.get("worker_wall_seconds")
    total = record.get("all_attempt_wall_seconds")
    if (not all(valid_seconds(value) for value in (attempt_budget, charged, prior, wall, total))
            or abs(attempt_budget - budget) > 1e-6 or charged != 0
            or abs(total - prior - wall) > 1e-6):
        return "attempt must receive the full timeout; prior elapsed time is audit-only"
    worker = record.get("worker_result")
    last_solve = record.get("final_attempt_solve_seconds")
    if (not isinstance(worker, dict) or worker.get("solve_seconds") != last_solve
            or (last_solve is not None and not valid_seconds(last_solve))):
        return "final attempt timing differs from the preserved worker result"
    if record.get("failure_kind") in {"resource_retry_budget_exhausted", "cumulative_time_limit"}:
        return "prior aborted attempts cannot exhaust a new attempt's timeout"
    if record.get("actual_status") in {"sat", "unsat"}:
        solve = record.get("solve_seconds")
        if (record.get("resource_aborted") or record.get("failure_kind") == "interrupted"
                or not valid_seconds(last_solve) or not valid_seconds(solve)
                or last_solve > budget or abs(solve - last_solve) > 1e-6):
            return "solved runtime must equal only the final non-aborted attempt's solve time"
    return None


def summarize(results_path: Path, plan_path: Path, output_dir: Path) -> dict[str, Any]:
    if (results_path.parent / ".runner.lock").exists():
        raise ValueError("run directory is locked; do not summarize while experiment records are being written")
    results_digest = sha256_file(results_path)
    plan_digest = sha256_file(plan_path)
    plan = read_json(plan_path)
    resource_policy = plan.get("parallel", {}).get("resource_policy", plan.get("merged_campaign", {}).get("resource_policy", {}))
    time_accounting = resource_policy.get("time_accounting")
    fingerprint = plan["fingerprint"]
    payload = {key: value for key, value in plan.items() if key not in {"fingerprint", "created_at"}}
    if digest_object(payload) != fingerprint:
        raise ValueError("run_plan.json fingerprint does not match its own contents")
    cases = {case["case_id"]: case for case in plan["cases"]}
    solvers = plan["solvers"]
    eligibility = get_eligibility(plan)
    violations: list[dict[str, Any]] = []
    latest: dict[tuple[str, str], dict[str, Any]] = {}
    seen_claims: dict[str, set[str]] = collections.defaultdict(set)
    previous_attempts: dict[tuple[str, str], int] = {}
    raw_count = 0

    def report(line: int | None, record: dict[str, Any], kind: str, detail: str) -> None:
        violation = {"line": line, "case_id": record.get("case_id"),
                     "solver": record.get("solver"), "kind": kind, "detail": detail}
        violations.append(violation)
        print(f"VIOLATION: line {line}: {violation['case_id']} {violation['solver']}: {detail}", file=sys.stderr)

    with results_path.open(encoding="utf-8-sig") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            raw_count += 1
            try:
                record = json.loads(line)
            except ValueError:
                report(line_number, {}, "invalid_json", "record is invalid JSON")
                continue
            if not isinstance(record, dict):
                report(line_number, {}, "invalid_record", "record is not an object")
                continue
            case_id, solver = record.get("case_id"), record.get("solver")
            if record.get("fingerprint") != fingerprint:
                report(line_number, record, "fingerprint_mismatch", "record belongs to a different experiment")
                continue
            if case_id not in cases or solver not in solvers:
                report(line_number, record, "unknown_job", "case_id or solver is absent from the run plan")
                continue
            case = cases[case_id]
            key = (case_id, solver)
            if not eligibility[key]["eligible"]:
                report(line_number, record, "not_applicable_job", "record was produced for a pair excluded by the run plan")
                continue
            status = record.get("actual_status")
            invalid = False
            expected_job = digest_object({"fingerprint": fingerprint, "case_id": case_id, "solver": solver})
            if record.get("job_key") != expected_job:
                report(line_number, record, "job_key_mismatch", "job_key does not match case, solver, and experiment")
                invalid = True
            for field in ("input_sha256", "expected_status", "benchmark", "family"):
                if record.get(field) != case.get(field):
                    report(line_number, record, "metadata_mismatch", f"{field} differs from the run plan")
                    invalid = True
            if record.get("seed") != plan["seed"] or record.get("timeout_seconds") != plan["timeout_seconds"]:
                report(line_number, record, "settings_mismatch", "seed or timeout differs from the run plan")
                invalid = True
            if (record.get("configuration_sha256") != plan["configuration_sha256"]
                    or record.get("code_fingerprint") != digest_object(plan["code"])):
                report(line_number, record, "code_config_mismatch", "code or configuration digest differs from the run plan")
                invalid = True
            if not isinstance(status, str) or status not in ACTUAL_STATUSES:
                report(line_number, record, "invalid_status", f"unsupported actual_status {status!r}")
                invalid = True
            if time_accounting == "per_attempt_full_budget_final_solve":
                error = attempt_timing_error(record, plan["timeout_seconds"])
                if error:
                    report(line_number, record, "attempt_timing_mismatch", error)
                    invalid = True
            attempt = record.get("attempt")
            if (not isinstance(attempt, int) or isinstance(attempt, bool) or attempt < 1
                    or attempt <= previous_attempts.get(key, 0)):
                report(line_number, record, "attempt_order", "attempt numbers are invalid, duplicated, or out of order")
                invalid = True
            else:
                previous_attempts[key] = attempt
            if status in {"sat", "unsat"}:
                seen_claims[case_id].add(status)
                seconds = record.get("solve_seconds")
                if not valid_seconds(seconds) or seconds > plan["timeout_seconds"]:
                    report(line_number, record, "invalid_timing", "successful claim has invalid or out-of-limit solver timing")
                    invalid = True
                if not valid_seconds(record.get("startup_seconds")):
                    report(line_number, record, "invalid_startup_timing", "successful claim has invalid startup timing")
                    invalid = True
                identity = plan.get("runtime_identity")
                metadata = record.get("solver_metadata")
                if identity and (not isinstance(metadata, dict)
                                 or any(metadata.get(key) != value for key, value in identity.items())):
                    report(line_number, record, "runtime_identity_mismatch", "worker runtime identity differs from the verified run plan")
                    invalid = True
            expected = case["expected_status"]
            conflict = status in {"sat", "unsat"} and expected in {"sat", "unsat"} and status != expected
            if conflict:
                report(line_number, record, "expected_status_conflict", f"expected {expected}, received {status}; excluded from solved counts")
            record["effective_status"] = "conflict" if conflict else "invalid" if invalid else status
            record["count_as_solved"] = not (conflict or invalid) and status in {"sat", "unsat"}
            latest[key] = record

    # An expected-unknown case may still expose contradictory claims across solvers/retries.
    conflicting_cases = {case_id for case_id, claims in seen_claims.items() if len(claims) > 1}
    for case_id in sorted(conflicting_cases):
        report(None, {"case_id": case_id}, "contradictory_solver_claims",
               "both SAT and UNSAT were reported for this same input; all its claims are excluded")
        for (cid, _), record in latest.items():
            if cid == case_id and record["actual_status"] in {"sat", "unsat"}:
                record["effective_status"] = "conflict"
                record["count_as_solved"] = False

    per_case = []
    # Keep every selected pair visible, but excluded pairs are not missing jobs.
    for case in plan["cases"]:
        for solver in solvers:
            record = latest.get((case["case_id"], solver))
            selection = eligibility[(case["case_id"], solver)]
            eligible = selection["eligible"]
            effective = "not_applicable" if not eligible else record["effective_status"] if record else "not_run"
            solved = bool(record and record["count_as_solved"])
            per_case.append({
                "case_id": case["case_id"], "solver": solver, "benchmark": case["benchmark"],
                "family": case["family"], "expected_status": case["expected_status"],
                "eligible": eligible, "eligibility_reason": selection["reason"],
                "case_policy": plan.get("case_policy", "all-pairs"),
                "actual_status": record.get("actual_status") if record else None,
                "effective_status": effective, "count_as_solved": solved,
                "solve_seconds": record.get("solve_seconds") if record else None,
                "startup_seconds": record.get("startup_seconds") if record else None,
                "worker_wall_seconds": record.get("worker_wall_seconds") if record else None,
                "prior_attempt_wall_seconds": record.get("prior_attempt_wall_seconds") if record else None,
                "all_attempt_wall_seconds": record.get("all_attempt_wall_seconds") if record else None,
                "resource_retry_count": record.get("resource_retry_count") if record else None,
                "timing_basis": record.get("timing_basis") if record else None,
                "stage": record.get("stage") if record else None,
                # CDF code must use only these successful runtimes. Unsolved values stay blank.
                "cdf_seconds": record.get("solve_seconds") if solved else None,
                "timeout_seconds": plan["timeout_seconds"],
                "attempt": record.get("attempt") if record else None,
                "failure_kind": record.get("failure_kind") if record else None,
                "reason": record.get("reason") if record else None,
                "availability": case["availability"], "input_sha256": case.get("input_sha256"),
                "fingerprint": fingerprint,
            })

    statuses = ("sat", "unsat", "unknown", "error", "timeout", "conflict", "invalid", "not_run", "not_applicable")

    def grouped_counts(dimensions: tuple[str, ...]) -> list[dict[str, Any]]:
        grouped: dict[tuple[Any, ...], list[dict[str, Any]]] = collections.defaultdict(list)
        for row in per_case:
            grouped[tuple(row[field] for field in dimensions)].append(row)
        output = []
        for key, values in sorted(grouped.items(), key=lambda item: tuple(str(x) for x in item[0])):
            counts = collections.Counter(row["effective_status"] for row in values)
            output.append({**dict(zip(dimensions, key)), "selected_cases": len(values),
                           "instances": sum(row["eligible"] for row in values),
                           "solved": sum(row["count_as_solved"] for row in values),
                           **{status: counts[status] for status in statuses}})
        return output

    by_solver = grouped_counts(("solver",))
    by_benchmark = grouped_counts(("solver", "benchmark"))
    by_family = grouped_counts(("solver", "benchmark", "family"))
    by_expected = grouped_counts(("solver", "benchmark", "expected_status"))
    stage_counts = collections.Counter((row["solver"], row["benchmark"], row["actual_status"], str(row["stage"]))
                                       for row in per_case if row["count_as_solved"])
    stages = [{"solver": key[0], "benchmark": key[1], "actual_status": key[2],
               "stage": key[3], "solved": count} for key, count in sorted(stage_counts.items())]
    if sha256_file(results_path) != results_digest or sha256_file(plan_path) != plan_digest:
        raise ValueError("run plan or raw results changed during validation; retry after the run stops")
    summary = {"schema_version": 1, "fingerprint": fingerprint, "raw_records": raw_count,
               "results_sha256": results_digest, "run_plan_sha256": plan_digest,
               "case_policy": plan.get("case_policy", "all-pairs"),
               "planned_jobs": sum(row["eligible"] for row in per_case),
               "selected_case_solver_pairs": len(per_case),
               "not_applicable": sum(not row["eligible"] for row in per_case),
               "violations": len(violations),
               "by_solver": by_solver, "by_benchmark": by_benchmark,
               "by_family": by_family, "by_expected_status": by_expected,
               "stage_counts": stages,
               "time_accounting": time_accounting,
               "execution_order": resource_policy.get("execution_order"),
               "solver_order": list(solvers),
               "runtime_policy": "Only checked SAT/UNSAT claims within the solve timeout count as solved. Startup is separate. CDFs use cdf_seconds only; blank values are unsolved."}
    if time_accounting == "per_attempt_full_budget_final_solve":
        summary["runtime_policy"] += " Each attempt receives the full solve timeout; only the final attempt's solver time enters comparisons. Prior aborted/interrupted attempts remain audit-only."
    output_dir.mkdir(parents=True, exist_ok=True)
    write_json(output_dir / "summary.json", summary)
    write_json(output_dir / "violations.json", violations)
    fields = list(per_case[0]) if per_case else ["case_id", "solver", "effective_status"]
    write_csv(output_dir / "per_case.csv", per_case, fields)
    count_fields = ["selected_cases", "instances", "solved", *statuses]
    for name, rows, dimensions in (
        ("by_solver.csv", by_solver, ["solver"]),
        ("by_benchmark.csv", by_benchmark, ["solver", "benchmark"]),
        ("by_family.csv", by_family, ["solver", "benchmark", "family"]),
        ("by_expected_status.csv", by_expected, ["solver", "benchmark", "expected_status"]),
    ):
        write_csv(output_dir / name, rows, [*dimensions, *count_fields])
    write_csv(output_dir / "stage_counts.csv", stages, ["solver", "benchmark", "actual_status", "stage", "solved"])
    write_csv(output_dir / "violations.csv", violations, ["line", "case_id", "solver", "kind", "detail"])
    return summary


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", required=True, type=Path)
    parser.add_argument("--plan", type=Path, help="Default: run_plan.json beside results.jsonl")
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        summary = summarize(args.results.resolve(),
                            (args.plan or args.results.parent / "run_plan.json").resolve(),
                            args.output_dir.resolve())
    except (OSError, ValueError, KeyError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    print(json.dumps({"fingerprint": summary["fingerprint"], "planned_jobs": summary["planned_jobs"],
                      "raw_records": summary["raw_records"], "violations": summary["violations"],
                      "by_solver": summary["by_solver"]}, indent=2, ensure_ascii=False))
    return 1 if summary["violations"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
