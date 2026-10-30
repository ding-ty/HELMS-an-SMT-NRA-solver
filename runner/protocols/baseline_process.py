"""Own each worker tree and release it when its attempt ends or Python dies."""
from __future__ import annotations
import ctypes as C
from ctypes import wintypes as W
import os
import signal
import subprocess


def pid_alive(pid):
    if not isinstance(pid, int) or pid <= 0:
        return False
    if os.name != 'nt':
        try:
            os.kill(pid, 0)
            return True
        except ProcessLookupError:
            return False
        except PermissionError:
            return True
    api = C.WinDLL('kernel32', use_last_error=True)
    api.OpenProcess.argtypes = [W.DWORD, W.BOOL, W.DWORD]
    api.OpenProcess.restype = W.HANDLE
    api.GetExitCodeProcess.argtypes = [W.HANDLE, C.POINTER(W.DWORD)]
    api.CloseHandle.argtypes = [W.HANDLE]
    handle = api.OpenProcess(0x1000, False, pid)
    if not handle:
        if C.get_last_error() == 87:
            return False
        if C.get_last_error() == 5:
            return True
        return False
    code = W.DWORD()
    try:
        if not api.GetExitCodeProcess(handle, C.byref(code)):
            raise OSError(C.get_last_error(), 'Cannot inspect existing process')
        return code.value == 259
    finally:
        api.CloseHandle(handle)


def memory_available_mb():
    if os.name == 'nt':
        class Memory(C.Structure):
            _fields_ = [('size', W.DWORD), ('load', W.DWORD)] + [(n, C.c_ulonglong) for n in (
                'total_phys', 'avail_phys', 'total_pagefile', 'avail_pagefile',
                'total_virtual', 'avail_virtual', 'extended')]
        value = Memory()
        value.size = C.sizeof(value)
        api = C.WinDLL('kernel32', use_last_error=True)
        if not api.GlobalMemoryStatusEx(C.byref(value)):
            raise OSError(C.get_last_error(), 'GlobalMemoryStatusEx')
        return {'available_physical_mb': value.avail_phys / 1024**2,
                'available_commit_mb': value.avail_pagefile / 1024**2}
    if os.path.exists('/proc/meminfo'):
        with open('/proc/meminfo', encoding='ascii') as stream:
            fields = {line.split(':')[0]: int(line.split()[1]) for line in stream}
        return {'available_physical_mb': fields['MemAvailable'] / 1024,
                'available_commit_mb': (fields['MemAvailable'] + fields.get('SwapFree', 0)) / 1024}
    return {}


class WorkerProcess:
    def __init__(self, command, stdout, stderr, cwd, cpu=0):
        self.job = None
        self.api = None
        self.assigned = False
        flags = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
        env = os.environ.copy()
        for name in ('OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
            env[name] = '1'
        self.process = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=stderr,
                                        env=env, creationflags=flags, start_new_session=os.name != 'nt')
        try:
            if os.name == 'nt':
                class Basic(C.Structure):
                    _fields_ = [('process_time', C.c_int64), ('job_time', C.c_int64),
                                ('flags', W.DWORD), ('min_working', C.c_size_t), ('max_working', C.c_size_t),
                                ('active', W.DWORD), ('affinity', C.c_size_t), ('priority', W.DWORD), ('scheduling', W.DWORD)]
                class IO(C.Structure):
                    _fields_ = [(n, C.c_ulonglong) for n in ('read_ops', 'write_ops', 'other_ops', 'read_bytes', 'write_bytes', 'other_bytes')]
                class Extended(C.Structure):
                    _fields_ = [('basic', Basic), ('io', IO)] + [(n, C.c_size_t) for n in ('process_memory', 'job_memory', 'peak_process', 'peak_job')]
                self.api = C.WinDLL('kernel32', use_last_error=True)
                self.api.CreateJobObjectW.argtypes = [C.c_void_p, W.LPCWSTR]
                self.api.CreateJobObjectW.restype = W.HANDLE
                self.api.SetInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD]
                self.api.AssignProcessToJobObject.argtypes = [W.HANDLE, W.HANDLE]
                self.api.TerminateJobObject.argtypes = [W.HANDLE, W.UINT]
                self.api.CloseHandle.argtypes = [W.HANDLE]
                self.job = self.api.CreateJobObjectW(None, None)
                info = Extended()
                info.basic.flags = 0x2000 | 0x10  # KILL_ON_JOB_CLOSE and one CPU.
                info.basic.affinity = 1 << cpu
                if not self.job or not self.api.SetInformationJobObject(self.job, 9, C.byref(info), C.sizeof(info)):
                    raise OSError(C.get_last_error(), 'Cannot create worker job')
                if not self.api.AssignProcessToJobObject(self.job, W.HANDLE(int(self.process._handle))):
                    raise OSError(C.get_last_error(), 'Cannot own worker process tree')
                self.assigned = True
            elif hasattr(os, 'sched_setaffinity'):
                available = sorted(os.sched_getaffinity(0))
                if cpu >= len(available):
                    raise ValueError('CPU index outside available affinity set')
                os.sched_setaffinity(self.process.pid, {available[cpu]})
        except BaseException:
            self.close()
            raise

    @property
    def pid(self):
        return self.process.pid

    def poll(self):
        return self.process.poll()

    def close(self):
        try:
            if self.process.poll() is None:
                if self.job and self.assigned:
                    if not self.api.TerminateJobObject(self.job, 0xE0000001):
                        # Keep cleanup effective even if job termination fails.
                        # Closing our last job handle below releases descendants.
                        self.process.kill()
                elif os.name != 'nt':
                    try:
                        os.killpg(self.process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                else:
                    # An existing job handle does not mean assignment succeeded.
                    # A worker rejected by AssignProcessToJobObject is still ours.
                    self.process.kill()
            try:
                self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                if self.job:
                    self.api.CloseHandle(self.job)
                    self.job = None
                    self.assigned = False
                if self.process.poll() is None:
                    self.process.kill()
                self.process.wait(timeout=10)
        finally:
            if self.job:
                self.api.CloseHandle(self.job)
                self.job = None
            self.assigned = False
