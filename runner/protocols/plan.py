#!/usr/bin/env python3
"""Portable campaign identity and balanced, disjoint experiment partitions.

The original runner's local plan remains intact, including every eligible pair.
Only the extra ``parallel`` envelope selects this machine's jobs.  Its campaign
identity omits installation paths, while retaining code/input/configuration and
resource-policy hashes.  No worker receives expected benchmark answers.
"""
from __future__ import annotations

from collections import defaultdict
import copy
from pathlib import Path
from typing import Any

try:
    from . import core as serial
except ImportError:
    import core as serial


def _relative_path(value: str, package_root: str | Path) -> str:
    """Handle Linux plans when the merge itself runs on Windows, and vice versa."""
    path = str(value).replace("\\", "/")
    root = str(package_root).replace("\\", "/").rstrip("/")
    # Windows drive letters and directory names are case insensitive.
    windows = len(root) > 1 and root[1] == ":"
    candidate, prefix = (path.casefold(), root.casefold()) if windows else (path, root)
    if candidate == prefix:
        return "."
    if candidate.startswith(prefix + "/"):
        return path[len(root) + 1:]
    # Portable merged plans already contain package-relative paths.
    if not path.startswith("/") and not (len(path) > 1 and path[1] == ":"):
        if ".." in path.split("/"):
            raise ValueError(f"path escapes package: {value}")
        return path
    raise ValueError(f"campaign code/input path is outside its package: {value}")


def _portable_projection(plan: dict[str, Any], resource_policy: dict[str, Any],
                         package_root: str | Path) -> dict[str, Any]:
    serial.get_eligibility(plan)
    cases = []
    for source in plan["cases"]:
        case = copy.deepcopy(source)
        if case.get("input_path") is not None:
            case["input_path"] = _relative_path(case["input_path"], package_root)
        cases.append(case)
    code = [{"path": _relative_path(row["path"], package_root), "sha256": row["sha256"]}
            for row in plan["code"]]
    code.sort(key=lambda row: row["path"])
    if len({row["path"] for row in code}) != len(code):
        raise ValueError("duplicate portable code path")
    runtime = plan.get("runtime_command", [])
    return {
        "schema_version": 1,
        "protocol": "stratified-disjoint-parallel-v1",
        "manifest_sha256": plan["manifest_sha256"],
        "cases": cases,
        "solvers": list(plan["solvers"]),
        "case_policy": plan["case_policy"],
        "eligibility": copy.deepcopy(plan["eligibility"]),
        "jobs": copy.deepcopy(plan["jobs"]),
        "seed": plan["seed"],
        "timeout_seconds": plan["timeout_seconds"],
        "startup_grace_seconds": plan["startup_grace_seconds"],
        "entrypoint": _relative_path(plan["entrypoint"], package_root),
        "runtime_arguments": list(runtime[1:]),
        "runtime_identity": copy.deepcopy(plan.get("runtime_identity")),
        "runtime_executable_sha256": plan.get("runtime_executable_sha256"),
        "launch_mode": plan["launch_mode"],
        "configuration": copy.deepcopy(plan["configuration"]),
        "configuration_sha256": plan["configuration_sha256"],
        "code": code,
        "python_version": plan.get("python_version"),
        "runner_platform": plan.get("runner_platform"),
        "resource_policy": copy.deepcopy(resource_policy),
    }


def _partition_jobs(payload: dict[str, Any], shards: int) -> list[dict[str, Any]]:
    if type(shards) is not int or shards < 1:
        raise ValueError("shards must be a positive integer")
    cases = {row["case_id"]: row for row in payload["cases"]}
    strata: dict[tuple[str, ...], list[tuple[int, dict[str, Any]]]] = defaultdict(list)
    for index, job in enumerate(payload["jobs"]):
        case = cases[job["case_id"]]
        stratum = tuple(str(value) for value in (
            case["benchmark"], case["expected_status"], case["family"], job["solver"]))
        strata[stratum].append((index, job))
    assigned = {}
    cursor = 0
    for key in sorted(strata):
        # Continue the round robin across strata so global shard sizes differ by
        # at most one, as do counts within every benchmark/status/family/solver.
        for index, job in sorted(strata[key], key=lambda item: item[1]["case_id"]):
            assigned[index] = {**job, "global_job_index": index, "shard_index": cursor % shards}
            cursor += 1
    return [assigned[index] for index in range(len(payload["jobs"]))]


def campaign_job_key(campaign: dict[str, Any], case_id: str, solver: str) -> str:
    return serial.digest_object({"campaign_fingerprint": campaign["fingerprint"],
                                 "case_id": case_id, "solver": solver})


def build_campaign(local_plan: dict[str, Any], resource_policy: dict[str, Any],
                   shards: int = 2, package_root: str | Path | None = None) -> dict[str, Any]:
    root = package_root if package_root is not None else serial.PACKAGE_ROOT
    payload = _portable_projection(local_plan, resource_policy, root)
    payload["shards"] = shards
    campaign = {"schema_version": 1, "fingerprint": serial.digest_object(payload), "payload": payload}
    campaign["jobs"] = [
        {**job, "campaign_job_key": campaign_job_key(campaign, job["case_id"], job["solver"])}
        for job in _partition_jobs(payload, shards)
    ]
    return campaign


def validate_campaign(campaign: dict[str, Any]) -> None:
    if not isinstance(campaign, dict) or campaign.get("schema_version") != 1:
        raise ValueError("invalid parallel campaign")
    payload = campaign.get("payload")
    if not isinstance(payload, dict) or serial.digest_object(payload) != campaign.get("fingerprint"):
        raise ValueError("campaign fingerprint does not match contents")
    expected = [{**job, "campaign_job_key": campaign_job_key(campaign, job["case_id"], job["solver"])}
                for job in _partition_jobs(payload, payload["shards"])]
    if campaign.get("jobs") != expected:
        raise ValueError("campaign job partition differs from its deterministic assignment")


def shard_jobs(campaign: dict[str, Any], shard_index: int) -> list[dict[str, Any]]:
    validate_campaign(campaign)
    shards = campaign["payload"]["shards"]
    if type(shard_index) is not int or not 0 <= shard_index < shards:
        raise ValueError(f"shard_index must be between 0 and {shards - 1}")
    return [copy.deepcopy(job) for job in campaign["jobs"] if job["shard_index"] == shard_index]


def attach_parallel_plan(local_plan: dict[str, Any], resource_policy: dict[str, Any],
                         shard_index: int, shards: int = 2,
                         package_root: str | Path | None = None) -> dict[str, Any]:
    root = Path(package_root) if package_root is not None else serial.PACKAGE_ROOT
    plan = copy.deepcopy(local_plan)
    if "parallel" in plan:
        raise ValueError("plan is already partitioned")
    # Include every scheduler/protocol/resource module, without cache/temp files.
    existing = {str(Path(row["path"]).resolve()): row for row in plan["code"]}
    for path in (root / "runner").glob("*.py"):
        resolved = str(path.resolve())
        existing[resolved] = {"path": resolved, "sha256": serial.sha256_file(path)}
    plan["code"] = sorted(existing.values(), key=lambda row: row["path"])
    campaign = build_campaign(plan, resource_policy, shards, root)
    selected = shard_jobs(campaign, shard_index)
    plan["parallel"] = {
        "schema_version": 1, "campaign": campaign, "shard_index": shard_index,
        "shards": shards, "assigned_job_indices": [row["global_job_index"] for row in selected],
        "resource_policy": copy.deepcopy(resource_policy), "package_root": str(root.resolve()),
    }
    payload = {key: value for key, value in plan.items() if key not in {"fingerprint", "created_at"}}
    plan["fingerprint"] = serial.digest_object(payload)
    return plan


# Both spellings are intentionally exported for callers using the design notes.
make_parallel_plan = attach_parallel_plan


def validate_local_campaign(plan: dict[str, Any]) -> dict[str, Any]:
    payload = {key: value for key, value in plan.items() if key not in {"fingerprint", "created_at"}}
    if serial.digest_object(payload) != plan.get("fingerprint"):
        raise ValueError("local run plan fingerprint does not match contents")
    parallel = plan.get("parallel")
    if not isinstance(parallel, dict):
        raise ValueError("run plan has no parallel campaign")
    campaign = parallel["campaign"]
    validate_campaign(campaign)
    rebuilt = build_campaign(plan, parallel["resource_policy"], parallel["shards"], parallel["package_root"])
    if rebuilt != campaign:
        raise ValueError("local code/inputs/configuration/resources differ from campaign")
    expected = [job["global_job_index"] for job in shard_jobs(campaign, parallel["shard_index"])]
    if parallel.get("assigned_job_indices") != expected:
        raise ValueError("assigned job indices differ from deterministic shard")
    return campaign


def assigned_jobs(plan: dict[str, Any]) -> list[dict[str, Any]]:
    campaign = validate_local_campaign(plan)
    return shard_jobs(campaign, plan["parallel"]["shard_index"])
