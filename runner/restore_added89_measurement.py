#!/usr/bin/env python3
"""Restore the measured 89-input Ubuntu package without changing solver bytes.

This creates a new working directory; it never launches a solver, overwrites an
existing directory, or copies the 89 unselected inputs. The historical measured
controller and its configuration are preserved, rather than replaced by the
repository's separate Windows batch entry point.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shlex
import sys
import tarfile


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_ID = "ev-769c58c2f7dc0958"
EXPECTED_ARCHIVE_SHA256 = "769c58c2f7dc095845dd23e0041028772731dbe08935d1926f586d4fab316e99"
METHODS = {"HELMS", "2D-LS", "V1", "V2", "V3", "V4", "V5", "LIMBS", "OpenCAD"}
HASH = re.compile(r"[0-9a-f]{64}\Z")


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def safe_name(name: str) -> str:
    require(isinstance(name, str) and bool(name), "Empty/non-string member name")
    path = PurePosixPath(name)
    require(not path.is_absolute() and path.as_posix() == name
            and all(part not in {"", ".", ".."} for part in path.parts)
            and "\\" not in name and ":" not in name and "\x00" not in name,
            "Unsafe archive/index path: " + repr(name))
    return name


def parse_json(raw: bytes):
    def unique_pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "Duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(raw.decode("utf-8-sig"), object_pairs_hook=unique_pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(
                          ValueError("Non-finite JSON value: " + value)))


def mapped_name(name: str) -> str | None:
    if name.startswith("measured/runner/"):
        return safe_name("runner/" + name.removeprefix("measured/runner/"))
    if name.startswith("measured/source/"):
        return safe_name("source/" + name.removeprefix("measured/source/"))
    if name in {"provenance/config.json", "provenance/source_manifest.json"}:
        return name.removeprefix("provenance/")
    if name.startswith(("inputs/", "originals/", "smt2/")) or name == "selected_manifest.jsonl":
        return safe_name(name)
    return None


def checked_payloads(repository: Path):
    index = parse_json((repository / "data/evidence/index.json").read_bytes())
    entries = [entry for entry in index["archives"] if entry["evidence_id"] == EVIDENCE_ID]
    require(len(entries) == 1, "Expected one selected-89 evidence archive")
    entry = entries[0]
    archive_path = repository / safe_name(entry["path"])
    archive_path = archive_path.resolve(strict=True)
    require(archive_path.is_relative_to(repository.resolve()), "Archive escapes repository")
    require(entry["sha256"] == EXPECTED_ARCHIVE_SHA256, "Unexpected measurement archive identity")
    archive_hash = hashlib.sha256()
    with archive_path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            archive_hash.update(chunk)
    require(archive_path.stat().st_size == entry["bytes"]
            and archive_hash.hexdigest() == entry["sha256"], "Evidence archive size/hash mismatch")

    payloads = {}
    mapping = {}
    with tarfile.open(archive_path, "r:gz") as archive:
        members = archive.getmembers()
        names = [safe_name(member.name) for member in members]
        require(len(names) == len(set(names)), "Duplicate evidence archive members")
        require(all(member.isfile() for member in members), "Only regular archive members are accepted")
        require("CHECKSUMS.json" in names, "Evidence has no CHECKSUMS.json")
        checksums = parse_json(archive.extractfile("CHECKSUMS.json").read())
        require(isinstance(checksums, dict)
                and set(names) == set(checksums) | {"CHECKSUMS.json"},
                "Evidence checksum/member inventory mismatch")
        for name, details in checksums.items():
            safe_name(name)
            require(isinstance(details, dict) and type(details.get("bytes")) is int
                    and details["bytes"] >= 0
                    and isinstance(details.get("sha256"), str)
                    and HASH.fullmatch(details["sha256"]), "Invalid member checksum: " + name)
        for member in members:
            raw = archive.extractfile(member).read()
            if member.name != "CHECKSUMS.json":
                details = checksums[member.name]
                require(len(raw) == details["bytes"] and digest(raw) == details["sha256"],
                        "Evidence member size/hash mismatch: " + member.name)
            destination = mapped_name(member.name)
            if destination is not None:
                require(destination not in payloads, "Duplicate restored destination: " + destination)
                payloads[destination] = raw
                mapping[destination] = {"archive_member": member.name,
                                        "bytes": len(raw), "sha256": digest(raw)}

    manifest = [parse_json(line) for line in payloads["selected_manifest.jsonl"].splitlines()
                if line.strip()]
    require(len(manifest) == 89 and len({case["case_id"] for case in manifest}) == 89
            and len({case["group"] for case in manifest}) == 89
            and all(case.get("selection_rank") == 1 for case in manifest),
            "Expected exactly the 89 rank-one paper inputs")
    for directory, suffix, path_key, hash_key in (
            ("inputs", ".json", "input_path", "input_sha256"),
            ("originals", ".mpl.txt", "source_path", "source_sha256"),
            ("smt2", ".smt2", "smt2_path", "smt2_sha256")):
        expected = {f"{directory}/{case['case_id']}{suffix}" for case in manifest}
        actual = {name for name in payloads if name.startswith(directory + "/")}
        require(actual == expected, "Unselected or missing inputs in " + directory)
        for case in manifest:
            name = safe_name(case[path_key])
            require(name in expected and digest(payloads[name]) == case[hash_key],
                    "Selected input/manifest mismatch: " + case["case_id"])

    config = parse_json(payloads["config.json"])
    require(set(config["solvers"]) == METHODS, "Expected the nine measured methods")
    for method, details in config["solvers"].items():
        source = safe_name(details["solver_file"])
        require(source in payloads and digest(payloads[source]) == details["solver_sha256"],
                "Measured solver/config mismatch: " + method)
        if details["config_file"] is not None:
            source = safe_name(details["config_file"])
            require(source in payloads and digest(payloads[source]) == details["config_sha256"],
                    "Measured configuration mismatch: " + method)
    require(digest(payloads["runner/worker.wls"]) == config["worker_sha256"],
            "Measured worker hash mismatch")
    source_manifest_name = safe_name(config["source_manifest"])
    require(digest(payloads[source_manifest_name]) == config["source_manifest_sha256"],
            "Measured source manifest hash mismatch")
    source_manifest = parse_json(payloads[source_manifest_name])
    require({item["path"] for item in source_manifest["files"]}
            == {name for name in payloads if name.startswith("source/")},
            "Measured source-tree inventory mismatch")
    for item in source_manifest["files"]:
        source = safe_name(item["path"])
        require(len(payloads[source]) == item["bytes"] and digest(payloads[source]) == item["sha256"],
                "Measured source dependency mismatch: " + source)
    return entry, payloads, mapping, manifest, config, len(members)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path,
                        help="New directory with an existing parent; existing paths are refused")
    parser.add_argument("--repository-root", type=Path, default=ROOT,
                        help="Repository containing data/evidence (default: this script's repository)")
    args = parser.parse_args(argv)
    repository = args.repository_root.expanduser().resolve(strict=True)
    requested = args.output.expanduser().absolute()
    require(not requested.exists() and not requested.is_symlink(), "Output already exists; choose a new path")
    require(requested.parent.is_dir(), "Output parent must already exist")
    output = requested.parent.resolve(strict=True) / requested.name
    require(not output.exists() and not output.is_symlink(), "Resolved output already exists")
    # Complete archive, member, input and source checks before creating anything.
    entry, payloads, mapping, manifest, config, member_count = checked_payloads(repository)
    quoted = shlex.quote(str(output))
    commands = {
        "verify": f"cd {quoted} && python3 runner/run_subset.py verify",
        "preflight": f"cd {quoted} && python3 runner/run_subset.py preflight "
                     "--wolfram-command /absolute/path/to/math "
                     "--cgroup-parent /sys/fs/cgroup/your-empty-delegation",
        "run": f"cd {quoted} && python3 runner/run_subset.py run "
               "--wolfram-command /absolute/path/to/math "
               "--cgroup-parent /sys/fs/cgroup/your-empty-delegation "
               "--output /absolute/path/to/new-results-directory",
    }
    reproduction = {
        "schema_version": 1, "measurement_id": "m-f0ec6ec9aa3468d7",
        "source_evidence_id": EVIDENCE_ID, "source_archive": entry["path"],
        "source_archive_sha256": entry["sha256"], "all_evidence_members_checked": member_count,
        "selected_inputs": len(manifest), "selected_groups": len({case["group"] for case in manifest}),
        "methods": list(config["solvers"]), "actual_tasks": len(manifest) * len(config["solvers"]),
        "original_campaign_scope": config.get("scope"),
        "scope_note": "The unchanged config.json scope describes the original 178-input, "
                      "1602-task campaign. This restored package contains only the 89 "
                      "rank-one paper inputs. The original controller reads the restored "
                      "manifest and plans 89 inputs x 9 methods = 801 new attempts. "
                      "Historical observations are not copied into a new results directory.",
        "solver_configuration_worker_runner_bytes_unchanged": True,
        "unselected_inputs_copied": 0, "solver_started_by_restoration": False,
        "execution_target": "Ubuntu 24.04, Python 3.10+, writable delegated cgroup v2, Wolfram 14.0",
        "timing": "Original external monotonic launch-to-marker 60-second budget; includes "
                  "kernel startup, input/config parsing and source loading. Per-worker 4 GiB RAM, swap=0.",
        "notes": ["The repository's default Windows batch runner is a separate execution protocol.",
                  "Source/configuration/manifest payload bytes are preserved; only paths are restored.",
                  "No historical solver status, answer or elapsed time is changed.",
                  "Run verify first, then preflight. Starting run creates new observations and does "
                  "not promise identical random-search outcomes or timings on different machines.",
                  "The original source/ARTIFACT_MANIFEST.json is historical source metadata; "
                  "source_manifest.json is the measured snapshot inventory used by this controller."],
        "commands": commands, "restored_payloads": mapping,
    }
    output.mkdir()  # Atomic refusal of an existing output path; no deletion/overwrite.
    for name, raw in payloads.items():
        destination = output.joinpath(*PurePosixPath(name).parts)
        require(destination.resolve().is_relative_to(output), "Destination escaped output")
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("xb") as stream:
            stream.write(raw)
    with (output / "REPRODUCTION.json").open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(reproduction, stream, ensure_ascii=True, indent=2)
        stream.write("\n")
    print(json.dumps({"restored": str(output), "selected_inputs": 89, "methods": 9,
                      "actual_tasks": 801, "restored_files": len(payloads),
                      "evidence_members_verified": member_count,
                      "solver_started": False, "commands": commands}, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        print("ERROR: " + str(error), file=sys.stderr)
        raise SystemExit(2)
