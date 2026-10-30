#!/usr/bin/env python3
"""Native Windows nested Job Objects, CPU affinity and committed-memory control.

Children start suspended, enter both jobs, and only then execute solver code.
No process suspension is used during solving. All job handles are non-inheritable
and KILL_ON_JOB_CLOSE protects descendants if the coordinator is terminated.
Windows committed memory is not the Linux RAM+swap metric.
"""
from __future__ import annotations

import ctypes as C
from ctypes import wintypes as W
from dataclasses import dataclass, asdict
import json
import math
import os
from pathlib import Path
import struct
import subprocess
import sys
import time
from typing import Any

try:
    from .resources import (GIB, MIB, THREAD_ENV, ResourceConfig,
                                     ResourceError, GroupUsage, ResourceSnapshot,
                                     adaptive_highs)
except ImportError:
    from resources import (GIB, MIB, THREAD_ENV, ResourceConfig,
                                    ResourceError, GroupUsage, ResourceSnapshot,
                                    adaptive_highs)

SIZE = C.c_size_t
HANDLE = C.c_void_p
DWORD = C.c_uint32
ULONG64 = C.c_uint64
INVALID_HANDLE = C.c_void_p(-1).value
JOB_MEMORY = 0x200
JOB_AFFINITY = 0x10
KILL_ON_CLOSE = 0x2000
RESOURCE_EXIT = 0xE0000001
MEMORY_EXIT_CODES = {0xC0000017, 0xC000009A, 0xC000012D}


class MEMORYSTATUSEX(C.Structure):
    _fields_ = [('length', DWORD), ('load', DWORD)] + [(name, ULONG64) for name in (
        'total_phys', 'avail_phys', 'total_commit', 'avail_commit',
        'total_virtual', 'avail_virtual', 'extended_virtual')]


class BASIC_LIMIT(C.Structure):
    _fields_ = [('process_time', C.c_int64), ('job_time', C.c_int64),
                ('flags', DWORD), ('min_working_set', SIZE), ('max_working_set', SIZE),
                ('active_process_limit', DWORD), ('affinity', SIZE),
                ('priority_class', DWORD), ('scheduling_class', DWORD)]


class IO_COUNTERS(C.Structure):
    _fields_ = [(name, ULONG64) for name in ('read_ops', 'write_ops', 'other_ops',
                                          'read_bytes', 'write_bytes', 'other_bytes')]


class EXTENDED_LIMIT(C.Structure):
    _fields_ = [('basic', BASIC_LIMIT), ('io', IO_COUNTERS),
                ('process_memory_limit', SIZE), ('job_memory_limit', SIZE),
                ('peak_process_memory', SIZE), ('peak_job_memory', SIZE)]


class NOTIFICATION_LIMIT(C.Structure):
    _fields_ = [('read_bytes', ULONG64), ('write_bytes', ULONG64),
                ('job_time', C.c_int64), ('job_memory', ULONG64),
                ('tolerance', DWORD), ('interval', DWORD), ('flags', DWORD)]


class LIMIT_VIOLATION(C.Structure):
    _fields_ = [('flags', DWORD), ('violations', DWORD)] + [
        (name, ULONG64) for name in ('read_bytes', 'read_limit', 'write_bytes',
                                    'write_limit', 'job_time', 'time_limit',
                                    'job_memory', 'memory_limit')] + [
        ('tolerance', DWORD), ('tolerance_limit', DWORD)]


class COMPLETION_ASSOCIATION(C.Structure):
    _fields_ = [('key', C.c_void_p), ('port', HANDLE)]


class PROCESS_MEMORY(C.Structure):
    _fields_ = [('cb', DWORD), ('faults', DWORD)] + [(name, SIZE) for name in (
        'peak_working_set', 'working_set', 'peak_paged_pool', 'paged_pool',
        'peak_nonpaged_pool', 'nonpaged_pool', 'pagefile_usage',
        'peak_pagefile_usage', 'private_usage')]


class THREADENTRY32(C.Structure):
    _fields_ = [('size', DWORD), ('usage', DWORD), ('thread_id', DWORD),
                ('process_id', DWORD), ('base_priority', C.c_int32),
                ('delta_priority', C.c_int32), ('flags', DWORD)]


class WinAPI:
    def __init__(self):
        if os.name != 'nt' or C.sizeof(C.c_void_p) != 8:
            raise ResourceError('Windows experiments require native 64-bit Windows Python; do not run through WSL')
        self.k = C.WinDLL('kernel32', use_last_error=True)
        self.p = C.WinDLL('psapi', use_last_error=True)
        declarations = {
            'CreateJobObjectW': ([C.c_void_p, W.LPCWSTR], HANDLE),
            'SetInformationJobObject': ([HANDLE, C.c_int, C.c_void_p, DWORD], W.BOOL),
            'QueryInformationJobObject': ([HANDLE, C.c_int, C.c_void_p, DWORD, C.c_void_p], W.BOOL),
            'AssignProcessToJobObject': ([HANDLE, HANDLE], W.BOOL),
            'IsProcessInJob': ([HANDLE, HANDLE, C.POINTER(W.BOOL)], W.BOOL),
            'TerminateJobObject': ([HANDLE, W.UINT], W.BOOL),
            'CloseHandle': ([HANDLE], W.BOOL),
            'GlobalMemoryStatusEx': ([C.POINTER(MEMORYSTATUSEX)], W.BOOL),
            'CreateMutexW': ([C.c_void_p, W.BOOL, W.LPCWSTR], HANDLE),
            'ReleaseMutex': ([HANDLE], W.BOOL),
            'WaitForSingleObject': ([HANDLE, DWORD], DWORD),
            'GetCurrentProcess': ([], HANDLE),
            'GetProcessAffinityMask': ([HANDLE, C.POINTER(SIZE), C.POINTER(SIZE)], W.BOOL),
            'GetLogicalProcessorInformationEx': ([C.c_int, C.c_void_p, C.POINTER(DWORD)], W.BOOL),
            'OpenProcess': ([DWORD, W.BOOL, DWORD], HANDLE),
            'CreateToolhelp32Snapshot': ([DWORD, DWORD], HANDLE),
            'Thread32First': ([HANDLE, C.POINTER(THREADENTRY32)], W.BOOL),
            'Thread32Next': ([HANDLE, C.POINTER(THREADENTRY32)], W.BOOL),
            'OpenThread': ([DWORD, W.BOOL, DWORD], HANDLE),
            'ResumeThread': ([HANDLE], DWORD),
            'CreateIoCompletionPort': ([HANDLE, HANDLE, SIZE, DWORD], HANDLE),
            'GetQueuedCompletionStatus': ([HANDLE, C.POINTER(DWORD), C.POINTER(SIZE),
                                           C.POINTER(C.c_void_p), DWORD], W.BOOL),
        }
        for name, (args, result) in declarations.items():
            method = getattr(self.k, name)
            method.argtypes, method.restype = args, result
        self.p.GetProcessMemoryInfo.argtypes = [HANDLE, C.c_void_p, DWORD]
        self.p.GetProcessMemoryInfo.restype = W.BOOL

    def check(self, ok, operation):
        if not ok:
            raise ResourceError(f'{operation}: {C.WinError(C.get_last_error())}')
        return ok

    def close(self, handle):
        if handle and handle != INVALID_HANDLE:
            self.check(self.k.CloseHandle(handle), 'CloseHandle')

    def query(self, handle, info_class, structure):
        self.check(self.k.QueryInformationJobObject(handle, info_class, C.byref(structure),
                                                  C.sizeof(structure), None), 'QueryInformationJobObject')
        return structure

    def set(self, handle, info_class, structure):
        self.check(self.k.SetInformationJobObject(handle, info_class, C.byref(structure),
                                                C.sizeof(structure)), 'SetInformationJobObject')

    def memory(self):
        value = MEMORYSTATUSEX()
        value.length = C.sizeof(value)
        self.check(self.k.GlobalMemoryStatusEx(C.byref(value)), 'GlobalMemoryStatusEx')
        return value

    def cpus(self, count):
        process, system = SIZE(), SIZE()
        self.check(self.k.GetProcessAffinityMask(self.k.GetCurrentProcess(), C.byref(process), C.byref(system)), 'GetProcessAffinityMask')
        size = DWORD()
        self.k.GetLogicalProcessorInformationEx(0, None, C.byref(size))
        buffer = C.create_string_buffer(size.value)
        self.check(self.k.GetLogicalProcessorInformationEx(0, buffer, C.byref(size)), 'GetLogicalProcessorInformationEx')
        cores = []
        offset = 0
        while offset < size.value:
            relationship, length = struct.unpack_from('<II', buffer.raw, offset)
            if not length:
                raise ResourceError('Invalid Windows CPU topology record')
            if relationship == 0:
                group_count = struct.unpack_from('<H', buffer.raw, offset + 30)[0]
                for index in range(group_count):
                    mask, group = struct.unpack_from('<QH', buffer.raw, offset + 32 + 16 * index)
                    if group != 0:
                        raise ResourceError('This four-core runner supports processor group 0 only (up to 64 logical CPUs)')
                    allowed = mask & process.value
                    if allowed:
                        cores.append((allowed & -allowed).bit_length() - 1)
            offset += length
        if len(cores) < count:
            raise ResourceError(f'Need {count} distinct accessible physical cores; found {len(cores)}')
        return cores[:count]

    def processes(self, job):
        capacity = 128
        while capacity <= 65536:
            buffer = C.create_string_buffer(8 + capacity * C.sizeof(SIZE))
            if self.k.QueryInformationJobObject(job, 3, buffer, len(buffer), None):
                assigned, returned = struct.unpack_from('<II', buffer.raw)
                return list(struct.unpack_from('<' + 'Q' * returned, buffer.raw, 8))
            if C.get_last_error() != 234:
                self.check(False, 'Query job process list')
            capacity *= 2
        raise ResourceError('Unexpectedly large worker process tree')

    def resume(self, pid):
        snapshot = self.k.CreateToolhelp32Snapshot(4, 0)
        if snapshot == INVALID_HANDLE:
            self.check(False, 'CreateToolhelp32Snapshot')
        found = 0
        try:
            entry = THREADENTRY32()
            entry.size = C.sizeof(entry)
            ok = self.k.Thread32First(snapshot, C.byref(entry))
            while ok:
                if entry.process_id == pid:
                    thread = self.k.OpenThread(2, False, entry.thread_id)
                    self.check(thread, 'OpenThread')
                    try:
                        result = self.k.ResumeThread(thread)
                        if result == 0xFFFFFFFF:
                            self.check(False, 'ResumeThread')
                        found += 1
                    finally:
                        self.close(thread)
                ok = self.k.Thread32Next(snapshot, C.byref(entry))
        finally:
            self.close(snapshot)
        if not found:
            raise ResourceError('Suspended worker primary thread was not found; refusing an unprotected launch')


@dataclass
class WindowsUsage(GroupUsage):
    working_set_bytes: int = 0
    private_commit_bytes: int = 0
    process_count: int = 0

    @property
    def oom_killed(self):
        # Common scheduler's status property means a resource-limit condition.
        # These are Windows limit events, not a claim of Linux OOM-killer action.
        return self.events.get('job_memory_limit', 0) > 0 or self.events.get('memory_exit_status', 0) > 0

    def to_dict(self):
        return {**asdict(self), 'memory_metric': 'private_committed_bytes',
                'swap_metric': 'not_separately_observable_on_windows'}


@dataclass
class WindowsSnapshot(ResourceSnapshot):
    available_commit_bytes: int = 0
    total_commit_limit_bytes: int = 0
    working_set_bytes: int = 0

    def to_dict(self):
        result = asdict(self)
        result['groups'] = {str(k): v.to_dict() for k, v in self.groups.items()}
        result['memory_metric'] = 'private_committed_bytes'
        return result


@dataclass
class WindowsProcess:
    process: subprocess.Popen
    slot: int
    job: Any
    cpu: int
    high: int
    key: int
    events: dict

    @property
    def cgroup(self):
        # Retain the common record field without pretending this is a cgroup.
        return f'WindowsJobObject/worker-{self.slot}'


class WindowsResources:
    def __init__(self, config: ResourceConfig, run_id: str):
        self.config = config
        self.run_id = run_id
        self.api = None
        self.parent = None
        self.port = None
        self.mutex = None
        self.locked = False
        self.managed = {}
        self.cpus = []
        self.prepared = False
        self.commit_budget = int(getattr(config, 'commit_budget_gib', 32.) * GIB)
        self.ram_budget = 0
        self.swap_budget = 0
        self.parent_events = {}
        self.next_key = 2

    def _new_job(self, mask, key, high):
        job = self.api.k.CreateJobObjectW(None, None)
        self.api.check(job, 'CreateJobObjectW')
        try:
            limits = EXTENDED_LIMIT()
            limits.basic.flags = KILL_ON_CLOSE | JOB_MEMORY | JOB_AFFINITY
            limits.basic.affinity = mask
            limits.job_memory_limit = self.commit_budget
            self.api.set(job, 9, limits)
            self.api.set(job, 7, COMPLETION_ASSOCIATION(key, self.port))
            self._set_notification(job, high)
            return job
        except BaseException:
            self.api.close(job)
            raise

    def _set_notification(self, job, high):
        info = NOTIFICATION_LIMIT()
        info.flags = JOB_MEMORY
        info.job_memory = high
        self.api.set(job, 12, info)

    def _drain(self):
        if not self.port:
            return
        keys = {item.key: item for item in self.managed.values()}
        for _ in range(8192):
            message, key, payload = DWORD(), SIZE(), C.c_void_p()
            ok = self.api.k.GetQueuedCompletionStatus(self.port, C.byref(message), C.byref(key), C.byref(payload), 0)
            if not ok:
                if C.get_last_error() == 258:
                    return
                self.api.check(False, 'GetQueuedCompletionStatus')
            item = keys.get(key.value)
            if item is None and key.value != 1:
                continue  # Delayed notifications from an already closed worker.
            events = item.events if item else self.parent_events
            if message.value in (9, 10):
                events['job_memory_limit'] = events.get('job_memory_limit', 0) + 1
            elif message.value == 11:
                handle = item.job if item else self.parent if key.value == 1 else None
                if handle:
                    violation = self.api.query(handle, 13, LIMIT_VIOLATION())
                    if violation.violations & JOB_MEMORY:
                        events['soft_notification'] = events.get('soft_notification', 0) + 1

    def prepare(self):
        self.api = WinAPI()
        if not 1 <= self.config.max_workers <= 4:
            raise ResourceError('workers must be between 1 and 4')
        numbers = (self.config.commit_budget_gib, self.config.reserve_commit_gib,
                   self.config.reserve_ram_gib, self.config.minimum_worker_gib,
                   self.config.pressure_available_gib)
        if (not all(math.isfinite(n) and n >= 0 for n in numbers)
                or self.commit_budget <= 0 or self.config.minimum_worker_gib <= 0
                or self.config.minimum_worker_gib * GIB > self.commit_budget):
            raise ResourceError('Invalid Windows resource budget')
        try:
            self.mutex = self.api.k.CreateMutexW(None, False, 'Global\\HELMSAdaptiveExperimentsWindowsV1')
            self.api.check(self.mutex, 'CreateMutexW')
            status = self.api.k.WaitForSingleObject(self.mutex, 0)
            if status not in (0, 0x80):
                raise ResourceError('Another Windows HELMS coordinator/doctor is active on this computer')
            self.locked = True
            memory = self.api.memory()
            reserve = int(getattr(self.config, 'reserve_commit_gib', 4.) * GIB)
            if self.commit_budget + reserve > memory.total_commit:
                raise ResourceError(f'Windows commit limit is {memory.total_commit/GIB:.2f} GiB; need at least {(self.commit_budget+reserve)/GIB:.2f} GiB. Configure the same larger Windows pagefile on both computers, then retry. RAM and pagefile are distinct.')
            self.ram_budget = max(0, (int(memory.total_phys) - int(self.config.reserve_ram_gib * GIB)) // GIB * GIB)
            self.cpus = self.api.cpus(self.config.max_workers)
            self.port = self.api.k.CreateIoCompletionPort(INVALID_HANDLE, None, 0, 1)
            self.api.check(self.port, 'CreateIoCompletionPort')
            self.parent = self._new_job(sum(1 << cpu for cpu in self.cpus), 1, int(self.commit_budget * .9))
            self.prepared = True
            probe = self.spawn([sys.executable, '-c', 'import os,json; print(json.dumps({"pid":os.getpid()}))'],
                               cwd=Path.cwd(), env=os.environ, slot=0,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = probe.process.communicate(timeout=15)
            if probe.process.returncode:
                raise ResourceError('Protected Windows launch failed: ' + err.decode(errors='replace'))
            data = json.loads(out)
            if data['pid'] != probe.process.pid:
                raise ResourceError('Protected Windows launch returned an unexpected PID')
            self.finish(0)
            return self.describe(memory)
        except BaseException:
            self.close()
            raise

    def describe(self, memory=None):
        memory = memory or self.api.memory()
        import winreg
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r'HARDWARE\DESCRIPTION\System\CentralProcessor\0') as key:
            model = winreg.QueryValueEx(key, 'ProcessorNameString')[0].strip()
        return {
            'backend': 'windows-job-objects', 'config': asdict(self.config),
            'host': {name: int(getattr(memory, name)) for name in (
                'total_phys', 'avail_phys', 'total_commit', 'avail_commit')},
            'ram_budget_bytes': self.ram_budget, 'swap_budget_bytes': None,
            'commit_budget_bytes': self.commit_budget,
            'cpus': self.cpus, 'cpu_models': [model],
            'kernel': list(sys.getwindowsversion()[:3]),
            'cpu_limit_backend': 'nested-job-affinity',
            'thread_environment': dict(THREAD_ENV),
            'memory_semantics': 'aggregate private commit; working set separately sampled; no Linux swap quota',
        }

    def spawn(self, argv, *, cwd, env, slot, stdout=None, stderr=None):
        if not self.prepared or slot in self.managed or not 0 <= slot < self.config.max_workers:
            raise ResourceError('Invalid or occupied Windows worker slot')
        key = self.next_key
        self.next_key += 1
        high = max(int(self.config.minimum_worker_gib * GIB), self.commit_budget // (len(self.managed) + 1))
        handle = self._new_job(1 << self.cpus[slot], key, high)
        process = None
        try:
            child_env = dict(env)
            child_env.update(THREAD_ENV)
            process = subprocess.Popen(list(map(str, argv)), cwd=str(cwd), env=child_env,
                                       stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL,
                                       creationflags=0x4 | subprocess.CREATE_NO_WINDOW | subprocess.CREATE_NEW_PROCESS_GROUP,
                                       close_fds=True)
            self.api.check(self.api.k.AssignProcessToJobObject(self.parent, int(process._handle)), 'Assign parent Job Object')
            self.api.check(self.api.k.AssignProcessToJobObject(handle, int(process._handle)), 'Assign single-CPU child Job Object')
            item = WindowsProcess(process, slot, handle, self.cpus[slot], high, key, {})
            self.managed[slot] = item
            self.api.resume(process.pid)
            return item
        except BaseException:
            if process is not None:
                process.kill()
                process.wait()
            if slot in self.managed:
                del self.managed[slot]
            self.api.close(handle)
            raise

    def contains_pid(self, slot, pid):
        process = self.api.k.OpenProcess(0x1000, False, pid)
        self.api.check(process, 'Open kernel PID')
        try:
            contained = W.BOOL()
            self.api.check(self.api.k.IsProcessInJob(process, self.managed[slot].job, C.byref(contained)), 'IsProcessInJob')
            return bool(contained.value)
        finally:
            self.api.close(process)

    def usage(self, slot):
        self._drain()
        item = self.managed[slot]
        limits = self.api.query(item.job, 9, EXTENDED_LIMIT())
        pids = self.api.processes(item.job)
        commit, resident = 0, 0
        for pid in pids:
            process = self.api.k.OpenProcess(0x100410, False, pid)
            if not process:
                if C.get_last_error() in (87, 1168):
                    continue  # It exited between the job snapshot and OpenProcess.
                self.api.check(False, 'Read protected process memory')
            try:
                info = PROCESS_MEMORY()
                info.cb = C.sizeof(info)
                if self.api.p.GetProcessMemoryInfo(process, C.byref(info), C.sizeof(info)):
                    commit += info.private_usage
                    resident += info.working_set
                elif self.api.k.WaitForSingleObject(process, 0) != 0:
                    self.api.check(False, 'GetProcessMemoryInfo for an active worker')
            finally:
                self.api.close(process)
        code = item.process.poll()
        if code is not None and (code & 0xFFFFFFFF) in MEMORY_EXIT_CODES:
            item.events['memory_exit_status'] = 1
        return WindowsUsage(slot=slot, memory_current=commit, memory_peak=int(limits.peak_job_memory),
                            high=item.high, events=dict(item.events), cpu=item.cpu,
                            working_set_bytes=resident, private_commit_bytes=commit,
                            process_count=len(pids))

    get_usage = usage

    def rebalance(self):
        self._drain()
        groups = {slot: self.usage(slot) for slot in self.managed}
        highs = adaptive_highs({slot: item.private_commit_bytes for slot, item in groups.items()},
                               self.commit_budget, int(self.config.minimum_worker_gib * GIB))
        for slot, high in highs.items():
            item = self.managed[slot]
            if abs(high - item.high) >= 64 * MIB:
                self._set_notification(item.job, high)
                item.high = high
            groups[slot].high = item.high
        host = self.api.memory()
        total = sum(group.private_commit_bytes for group in groups.values())
        rss = sum(group.working_set_bytes for group in groups.values())
        reasons = []
        if host.avail_commit < max(GIB, int(self.config.pressure_available_gib * GIB)):
            reasons.append('windows_commit_headroom_low')
        if total >= int(self.commit_budget * (.9 if len(groups) > 1 else .98)):
            reasons.append('batch_commit_near_limit')
        if self.parent_events.get('job_memory_limit'):
            reasons.append('parent_job_memory_limit')
            self.parent_events.pop('job_memory_limit', None)
        # Physical RAM can be paged. Low RAM alone does not terminate a lone
        # worker when there is ample commit headroom for the pagefile.
        if len(groups) > 1 and host.avail_phys < int(self.config.pressure_available_gib * GIB):
            reasons.append('physical_ram_pressure_with_concurrent_workers')
        if any(group.oom_killed for group in groups.values()):
            reasons.append('worker_job_memory_limit')
        victim = max(groups, key=lambda slot: groups[slot].private_commit_bytes) if reasons and groups else None
        admit = (not reasons and len(groups) < self.config.max_workers
                 and host.avail_commit >= max(2 * GIB, int(self.config.minimum_worker_gib * GIB))
                 and host.avail_phys >= int((self.config.pressure_available_gib + self.config.minimum_worker_gib) * GIB)
                 and self.commit_budget - total >= GIB)
        return WindowsSnapshot(len(groups), int(host.avail_phys), total, 0, admit,
                               bool(reasons), victim, groups, reasons,
                               int(host.avail_commit), int(host.total_commit), rss)

    def kill(self, slot):
        before = self.usage(slot)
        self.api.check(self.api.k.TerminateJobObject(self.managed[slot].job, RESOURCE_EXIT), 'TerminateJobObject')
        self.managed[slot].process.wait(timeout=15)
        return before

    def finish(self, slot):
        item = self.managed[slot]
        if item.process.poll() is None:
            raise ResourceError('Cannot finish an active Windows worker')
        before = self.usage(slot)
        self.api.check(self.api.k.TerminateJobObject(item.job, RESOURCE_EXIT), 'Terminate descendants')
        deadline = time.monotonic() + 15
        while self.api.processes(item.job):
            if time.monotonic() > deadline:
                raise ResourceError('Windows descendants did not exit after job termination')
            time.sleep(.05)
        self.api.close(item.job)
        del self.managed[slot]
        return before

    def close(self):
        errors = []
        if not self.api:
            return
        for slot in list(self.managed):
            try:
                if self.managed[slot].process.poll() is None:
                    self.kill(slot)
                self.finish(slot)
            except (OSError, ResourceError, subprocess.SubprocessError) as exc:
                errors.append(str(exc))
        for name in ('parent', 'port'):
            handle = getattr(self, name)
            if handle:
                self.api.close(handle)
                setattr(self, name, None)
        if self.mutex:
            if self.locked:
                self.api.check(self.api.k.ReleaseMutex(self.mutex), 'Release resource mutex')
            self.api.close(self.mutex)
            self.mutex = None
            self.locked = False
        self.prepared = False
        if errors:
            raise ResourceError('Windows cleanup incomplete: ' + '; '.join(errors))
