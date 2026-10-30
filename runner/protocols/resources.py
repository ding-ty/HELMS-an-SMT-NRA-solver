#!/usr/bin/env python3
"""Linux cgroup-v2 isolation and conservative, adaptive experiment admission.

This module never suspends a solver.  Under pressure the scheduler may terminate
one attempt and retry it alone; elapsed-time limits therefore remain meaningful.
Hard group limits protect the guest from this batch, not from unrelated programs.
No finite machine can guarantee that every nonlinear instance fits in memory.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, field
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
from typing import Any, Mapping, Sequence

GIB = 1024 ** 3
MIB = 1024 ** 2
THREAD_ENV = {name: "1" for name in (
    "OMP_NUM_THREADS", "OMP_THREAD_LIMIT", "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS")}
REQUIRED_CONTROLLERS = ("memory", "cpuset")


class ResourceError(RuntimeError):
    """Protection unavailable: do not launch unprotected experiments."""


@dataclass(frozen=True)
class ResourceConfig:
    max_workers: int = 4
    reserve_ram_gib: float = 2.0
    reserve_swap_gib: float = 1.0
    minimum_worker_gib: float = 0.75
    pressure_available_gib: float = 0.75
    cgroup_parent: str = "/sys/fs/cgroup"
    poll_seconds: float = 0.5
    pressure_fraction: float = 0.90
    commit_budget_gib: float = 32.0
    reserve_commit_gib: float = 4.0


@dataclass(frozen=True)
class HostMemory:
    total: int
    available: int
    swap_total: int
    swap_free: int


@dataclass
class GroupUsage:
    slot: int
    memory_current: int = 0
    memory_peak: int = 0
    swap_current: int = 0
    high: int = 0
    events: dict[str, int] = field(default_factory=dict)
    events_local: dict[str, int] = field(default_factory=dict)
    pressure_some_avg10: float = 0.0
    pressure_full_avg10: float = 0.0
    cpu: int = -1

    @property
    def oom_killed(self) -> bool:
        return self.events.get("oom_kill", 0) > 0 or self.events.get("oom_group_kill", 0) > 0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ResourceSnapshot:
    active: int
    available: int
    memory_current: int
    swap_current: int
    admit_new: bool
    pressure: bool
    victim_slot: int | None
    groups: dict[int, GroupUsage]
    reasons: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["groups"] = {str(k): v.to_dict() for k, v in self.groups.items()}
        return value


@dataclass
class ManagedProcess:
    process: subprocess.Popen
    slot: int
    cgroup: Path
    cpu: int
    high: int


def parse_meminfo(text: str) -> HostMemory:
    values: dict[str, int] = {}
    for line in text.splitlines():
        fields = line.split()
        if len(fields) >= 2:
            values[fields[0].rstrip(":")] = int(fields[1]) * (1024 if len(fields) > 2 and fields[2] == "kB" else 1)
    if "MemTotal" not in values or "MemAvailable" not in values:
        raise ResourceError("/proc/meminfo must provide MemTotal and MemAvailable")
    return HostMemory(values["MemTotal"], values["MemAvailable"], values.get("SwapTotal", 0), values.get("SwapFree", 0))


def parse_events(text: str) -> dict[str, int]:
    return {parts[0]: int(parts[1]) for line in text.splitlines() if len(parts := line.split()) == 2}


def parse_pressure(text: str) -> dict[str, dict[str, float]]:
    result: dict[str, dict[str, float]] = {}
    for line in text.splitlines():
        fields = line.split()
        if fields:
            result[fields[0]] = {name: float(value) for token in fields[1:] if "=" in token for name, value in [token.split("=", 1)]}
    return result


def controller_enablement(available: Sequence[str], enabled: Sequence[str]) -> str:
    """Require hard CPU and memory isolation; never silently drop either."""
    missing = [name for name in REQUIRED_CONTROLLERS if name not in available]
    if missing:
        raise ResourceError("Required cgroup v2 controllers unavailable: " + ", ".join(missing))
    return " ".join("+" + name for name in REQUIRED_CONTROLLERS if name not in enabled)


def select_physical_cpus(allowed: Sequence[int], topology: Mapping[int, tuple[int, int]], count: int) -> list[int]:
    """Choose distinct cores in Linux's topology (WSL host mapping is opaque)."""
    selected: list[int] = []
    used: set[tuple[int, int]] = set()
    for cpu in sorted(allowed):
        if cpu not in topology:
            continue
        if topology[cpu] not in used:
            used.add(topology[cpu])
            selected.append(cpu)
            if len(selected) == count:
                return selected
    raise ResourceError(f"Need {count} allowed distinct cores in Linux's reported topology; found {len(selected)}")


def adaptive_highs(usages: Mapping[int, int], budget: int, minimum: int) -> dict[int, int]:
    """Water-fill available RAM towards observed demand with a small growth margin.

    Low-use jobs lend their unused soft allowance to growing jobs.  Hard limits
    are the shared parent budget; memory.high is only a reclaim/throttle target.
    """
    if not usages:
        return {}
    if budget < len(usages) * minimum:
        raise ResourceError("Active worker minimums exceed RAM budget")
    remaining = budget - len(usages) * minimum
    demand = {slot: max(0, used + 256 * MIB - minimum) for slot, used in usages.items()}
    demand_total = sum(demand.values())
    if demand_total <= remaining:
        spare = (remaining - demand_total) // len(usages)
        return {slot: minimum + want + spare for slot, want in demand.items()}
    return {slot: minimum + (remaining * want // demand_total) for slot, want in demand.items()}


def choose_pressure_action(*, host: HostMemory, groups: Mapping[int, GroupUsage],
                           total_memory: int, total_swap: int, ram_budget: int,
                           swap_budget: int, config: ResourceConfig) -> ResourceSnapshot:
    reasons: list[str] = []
    if host.available < int(config.pressure_available_gib * GIB):
        reasons.append("host_available_low")
    # Crossing RAM high alone is expected and can be relieved by reserved swap.
    # Terminate conservatively before both hard RAM and swap budgets are full.
    ram_busy = total_memory >= int(ram_budget * config.pressure_fraction)
    swap_busy = swap_budget == 0 or total_swap >= int(swap_budget * config.pressure_fraction)
    if ram_busy and swap_busy:
        reasons.append("batch_ram_and_swap_near_limit")
    if any(group.oom_killed for group in groups.values()):
        reasons.append("cgroup_oom_kill")
    if any(group.pressure_full_avg10 >= 20.0 for group in groups.values()) and ram_busy:
        reasons.append("sustained_memory_stall")
    pressure = bool(reasons)
    alive = [usage for usage in groups.values() if not usage.oom_killed]
    victim = max(alive, key=lambda item: item.memory_current + item.swap_current).slot if pressure and alive else None
    remaining_combined = max(0, ram_budget - total_memory) + max(0, swap_budget - total_swap)
    minimum = int(config.minimum_worker_gib * GIB)
    admission_headroom = max(minimum, GIB)
    admit = (not pressure and len(groups) < config.max_workers
             and remaining_combined >= admission_headroom
             and host.available >= int(config.pressure_available_gib * GIB) + minimum)
    return ResourceSnapshot(len(groups), host.available, total_memory, total_swap,
                            admit, pressure, victim, dict(groups), reasons)


class LinuxResources:
    """Own a bounded cgroup tree. prepare()/close() must surround all launches."""

    def __init__(self, config: ResourceConfig, run_id: str):
        if not re.fullmatch(r"[A-Za-z0-9_-]{1,100}", run_id):
            raise ValueError("run_id must contain 1-100 ASCII letters, digits, underscore or hyphen")
        if not 1 <= config.max_workers <= 4:
            raise ValueError("max_workers must be between 1 and 4")
        if min(config.reserve_ram_gib, config.reserve_swap_gib) < 0 or config.minimum_worker_gib <= 0:
            raise ValueError("Memory reserves must be nonnegative and minimum worker RAM positive")
        self.config = config
        self.root = Path(config.cgroup_parent)
        self.path = self.root / f"helms-parallel-{run_id}"
        self.managed: dict[int, ManagedProcess] = {}
        self.cpus: list[int] = []
        self.ram_budget = 0
        self.swap_budget = 0
        self.prepared = False
        self.owned = False
        self.lock_fd: int | None = None

    def _machine_lock(self) -> None:
        import fcntl  # Linux-only, deliberately not imported on Windows.
        lock_path = "/run/lock/helms-parallel-resources.lock"
        descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0), 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            os.close(descriptor)
            raise ResourceError("Another protected HELMS batch/doctor owns this machine; do not launch separate batches concurrently")
        self.lock_fd = descriptor

    def _refuse_orphaned_workers(self) -> None:
        # flock is released after SIGKILL, but the old cgroup and kernels remain.
        # Never hide this by allowing a second independent RAM budget.
        for group in Path("/sys/fs/cgroup").rglob("helms-parallel-*"):
            if not group.is_dir():
                continue
            events = parse_events((group / "cgroup.events").read_text(encoding="ascii"))
            if events.get("populated", 0):
                raise ResourceError("Live kernels remain in an earlier batch cgroup: " + str(group)
                                    + ". Stop that batch or explicitly clean up its workers before starting another.")

    @staticmethod
    def host_memory() -> HostMemory:
        return parse_meminfo(Path("/proc/meminfo").read_text(encoding="ascii"))

    @staticmethod
    def _integer(path: Path, default: int | None = None) -> int:
        try:
            return int(path.read_text(encoding="ascii").strip())
        except FileNotFoundError:
            if default is not None:
                return default
            raise

    @staticmethod
    def _write(path: Path, value: str | int) -> None:
        if path.name == "memory.high" and hasattr(os, "O_NONBLOCK"):
            # Avoid performing potentially lengthy direct reclaim in the
            # monitoring thread while reducing a soft allowance.
            descriptor = os.open(path, os.O_WRONLY | os.O_NONBLOCK)
            try:
                os.write(descriptor, str(value).encode("ascii"))
            finally:
                os.close(descriptor)
        else:
            path.write_text(str(value), encoding="ascii")

    def _ancestor_limit(self, name: str, fallback: int) -> int:
        """Respect enclosing containers/delegated cgroups as well as host RAM."""
        current = self.root.resolve()
        mount = Path("/sys/fs/cgroup").resolve()
        if current != mount and mount not in current.parents:
            raise ResourceError("cgroup_parent must be within /sys/fs/cgroup")
        limit = fallback
        while True:
            path = current / name
            if path.exists():
                raw = path.read_text(encoding="ascii").strip()
                if raw != "max":
                    limit = min(limit, int(raw))
            if current == mount:
                return limit
            current = current.parent

    def _cpu_selection(self) -> list[int]:
        topology: dict[int, tuple[int, int]] = {}
        allowed = sorted(os.sched_getaffinity(0))
        for cpu in allowed:
            base = Path(f"/sys/devices/system/cpu/cpu{cpu}/topology")
            try:
                topology[cpu] = (self._integer(base / "physical_package_id"), self._integer(base / "core_id"))
            except (OSError, ValueError):
                continue
        return select_physical_cpus(allowed, topology, self.config.max_workers)

    def _enable_controllers(self, group: Path) -> None:
        available = (group / "cgroup.controllers").read_text(encoding="ascii").split()
        enabled = (group / "cgroup.subtree_control").read_text(encoding="ascii").split()
        command = controller_enablement(available, enabled)
        if command:
            self._write(group / "cgroup.subtree_control", command)

    def _set_cpuset(self, group: Path, cpus: Sequence[int], mems: str) -> None:
        if not mems.strip():
            raise ResourceError("No effective cpuset memory nodes are available")
        # Configure allowed NUMA nodes before CPU placement and before joining.
        self._write(group / "cpuset.mems", mems.strip())
        self._write(group / "cpuset.cpus", ",".join(map(str, cpus)))

    def prepare(self) -> dict[str, Any]:
        if sys.platform != "linux" or not hasattr(os, "sched_setaffinity"):
            raise ResourceError("Protected parallel experiments require Linux cgroup v2 and CPU affinity; Windows is not supported")
        if self.prepared:
            raise ResourceError("Resources are already prepared")
        try:
            self._machine_lock()
            self._refuse_orphaned_workers()
            controllers = (self.root / "cgroup.controllers").read_text(encoding="ascii").split()
            controller_enablement(controllers, [])
            self.cpus = self._cpu_selection()
            host = self.host_memory()
            effective_ram = self._ancestor_limit("memory.max", host.total)
            effective_swap = self._ancestor_limit("memory.swap.max", host.swap_total)
            # Integral GiB budgets keep equivalent WSL hosts comparable despite
            # small boot-to-boot differences in kernel-reserved memory.
            self.ram_budget = ((effective_ram - int(self.config.reserve_ram_gib * GIB)) // GIB) * GIB
            self.swap_budget = (max(0, effective_swap - int(self.config.reserve_swap_gib * GIB)) // GIB) * GIB
            if self.ram_budget < self.config.max_workers * int(self.config.minimum_worker_gib * GIB):
                raise ResourceError("RAM after OS reserve is insufficient for the configured worker minimums")
            self._enable_controllers(self.root)
            self.path.mkdir()  # Refuse collisions, including another active scheduler.
            self.owned = True
            self._set_cpuset(self.path, self.cpus,
                             (self.root / "cpuset.mems.effective").read_text(encoding="ascii"))
            self._write(self.path / "memory.max", self.ram_budget)
            self._write(self.path / "memory.high", int(self.ram_budget * .92))
            self._write(self.path / "memory.swap.max", self.swap_budget)
            self._write(self.path / "memory.oom.group", 0)
            self._enable_controllers(self.path)
            if not (self.path / "cgroup.kill").exists():
                raise ResourceError("Kernel lacks cgroup.kill; refusing incomplete descendant cleanup")
            self.prepared = True
            # Launch a real disposable child through the same protected exec path.
            probe = self.spawn([sys.executable, "-c", "import os; print(os.getpid())"],
                               cwd=Path.cwd(), env=os.environ, slot=0,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = probe.process.communicate(timeout=15)
            if probe.process.returncode != 0:
                raise ResourceError("Protected launch probe failed: " + err.decode("utf-8", errors="replace"))
            self.finish(0)
            return self.describe(host)
        except ResourceError:
            self.close()
            raise
        except (OSError, ValueError, subprocess.SubprocessError) as exc:
            self.close()
            raise ResourceError(f"Cannot establish cgroup-v2 memory+cpuset protection: {exc}. Run as root or provide a delegated writable cgroup; never fall back to unprotected parallelism.") from exc

    def describe(self, host: HostMemory | None = None) -> dict[str, Any]:
        return {"backend": "cgroup-v2", "config": asdict(self.config), "cgroup": str(self.path),
                "host": asdict(host or self.host_memory()), "ram_budget_bytes": self.ram_budget,
                "swap_budget_bytes": self.swap_budget, "cpus": self.cpus,
                "cpu_limit_backend": "cgroup-v2-cpuset+process-affinity",
                "required_controllers": list(REQUIRED_CONTROLLERS),
                "thread_environment": dict(THREAD_ENV), "kernel": os.uname().release if sys.platform == "linux" else None}

    def spawn(self, argv: Sequence[str], *, cwd: Path | str, env: Mapping[str, str],
              slot: int, stdout: Any = None, stderr: Any = None) -> ManagedProcess:
        if not self.prepared:
            raise ResourceError("prepare() must pass before launching workers")
        if slot in self.managed or not 0 <= slot < self.config.max_workers:
            raise ResourceError(f"Slot {slot} is occupied or invalid")
        group = self.path / f"worker-{slot}"
        group.mkdir()
        try:
            self._set_cpuset(group, [self.cpus[slot]],
                             (self.path / "cpuset.mems.effective").read_text(encoding="ascii"))
            self._write(group / "memory.max", self.ram_budget)
            self._write(group / "memory.swap.max", self.swap_budget)
            self._write(group / "memory.oom.group", 1)
            high = max(int(self.config.minimum_worker_gib * GIB), self.ram_budget // (len(self.managed) + 1))
            self._write(group / "memory.high", high)
            child_env = dict(env)
            child_env.update(THREAD_ENV)
            command = [sys.executable, str(Path(__file__).resolve()), "_exec", "--cgroup", str(group),
                       "--cpu", str(self.cpus[slot]), "--", *map(str, argv)]
            process = subprocess.Popen(command, cwd=cwd, env=child_env, stdout=stdout,
                                       stderr=stderr, start_new_session=True)
            managed = ManagedProcess(process, slot, group, self.cpus[slot], high)
            self.managed[slot] = managed
            return managed
        except BaseException:
            group.rmdir()
            raise

    def usage(self, slot: int) -> GroupUsage:
        managed = self.managed[slot]
        pressure_file = managed.cgroup / "memory.pressure"
        pressure = parse_pressure(pressure_file.read_text(encoding="ascii")) if pressure_file.exists() else {}
        return GroupUsage(slot=slot,
                          memory_current=self._integer(managed.cgroup / "memory.current"),
                          memory_peak=self._integer(managed.cgroup / "memory.peak", 0),
                          swap_current=self._integer(managed.cgroup / "memory.swap.current"),
                          high=managed.high,
                          events=parse_events((managed.cgroup / "memory.events").read_text(encoding="ascii")),
                          events_local=parse_events((managed.cgroup / "memory.events.local").read_text(encoding="ascii")),
                          pressure_some_avg10=pressure.get("some", {}).get("avg10", 0.0),
                          pressure_full_avg10=pressure.get("full", {}).get("avg10", 0.0), cpu=managed.cpu)

    get_usage = usage

    def rebalance(self) -> ResourceSnapshot:
        if not self.prepared:
            raise ResourceError("Resource protection is not prepared")
        usages = {slot: self.usage(slot) for slot in self.managed}
        highs = adaptive_highs({slot: item.memory_current for slot, item in usages.items()},
                               self.ram_budget, int(self.config.minimum_worker_gib * GIB))
        for slot, high in highs.items():
            managed = self.managed[slot]
            # On older WSL kernels O_NONBLOCK may not avoid synchronous reclaim.
            # Only reduce a group with margin above its observed current use;
            # parent memory.max remains the shared hard budget at all times.
            if high < managed.high:
                high = min(self.ram_budget, max(high, usages[slot].memory_current + 256 * MIB))
            # Limit control-plane writes while retaining a useful dynamic target.
            if abs(high - managed.high) >= 64 * MIB:
                self._write(managed.cgroup / "memory.high", high)
                managed.high = high
            usages[slot].high = managed.high
        return choose_pressure_action(host=self.host_memory(), groups=usages,
                                      total_memory=self._integer(self.path / "memory.current"),
                                      total_swap=self._integer(self.path / "memory.swap.current"),
                                      ram_budget=self.ram_budget, swap_budget=self.swap_budget,
                                      config=self.config)

    def kill(self, slot: int) -> GroupUsage:
        """Terminate the entire cgroup; the scheduler records a resource attempt."""
        managed = self.managed[slot]
        before = self.usage(slot)
        self._write(managed.cgroup / "cgroup.kill", 1)
        try:
            managed.process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(managed.process.pid, signal.SIGKILL)
            managed.process.wait(timeout=10)
        return before

    def finish(self, slot: int) -> GroupUsage:
        managed = self.managed[slot]
        if managed.process.poll() is None:
            raise ResourceError("Cannot finish a running worker; kill or await it first")
        usage = self.usage(slot)
        # The top process may have exited while a linked process still lives.
        self._write(managed.cgroup / "cgroup.kill", 1)
        deadline = time.monotonic() + 10
        while True:
            try:
                managed.cgroup.rmdir()
                break
            except OSError:
                if time.monotonic() >= deadline:
                    raise ResourceError("Worker cgroup remains populated after cgroup.kill: " + str(managed.cgroup))
                time.sleep(.05)
        del self.managed[slot]
        return usage

    def close(self) -> None:
        """Clean every descendant; an incomplete cleanup is a visible error."""
        errors: list[str] = []
        for slot in list(self.managed):
            try:
                if self.managed[slot].process.poll() is None:
                    self.kill(slot)
                self.finish(slot)
            except (OSError, ResourceError, subprocess.SubprocessError) as exc:
                errors.append(f"slot {slot}: {exc}")
        try:
            if self.owned and self.path.exists():
                if (self.path / "cgroup.kill").exists():
                    self._write(self.path / "cgroup.kill", 1)
                self.path.rmdir()
                self.owned = False
        except OSError as exc:
            errors.append(str(exc))
        self.prepared = False
        if self.lock_fd is not None:
            os.close(self.lock_fd)
            self.lock_fd = None
        if errors:
            raise ResourceError("Incomplete cgroup cleanup; do not launch new kernels until resolved: " + "; ".join(errors))


def protected_exec(argv: Sequence[str]) -> None:
    parser = argparse.ArgumentParser(description="Internal protected worker launcher")
    parser.add_argument("--cgroup", required=True)
    parser.add_argument("--cpu", required=True, type=int)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command and args.command[0] == "--" else args.command
    if not command:
        raise ResourceError("Missing protected command")
    group = Path(args.cgroup)
    # Join before executing user/runtime code; every descendant inherits this.
    (group / "cgroup.procs").write_text(str(os.getpid()), encoding="ascii")
    os.sched_setaffinity(0, {args.cpu})
    for name, value in THREAD_ENV.items():
        os.environ[name] = value
    os.execvpe(command[0], command, os.environ)


if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "_exec":
        try:
            protected_exec(sys.argv[2:])
        except (OSError, ResourceError) as exc:
            print("Protected launcher failed: " + str(exc), file=sys.stderr)
            sys.exit(125)
    else:
        print("This module is used by parallel_experiments.py; it is not a solver.", file=sys.stderr)
        sys.exit(2)
