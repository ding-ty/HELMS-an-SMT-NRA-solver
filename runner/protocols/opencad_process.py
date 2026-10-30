"""Native Windows worker ownership, one CPU, fixed commit cap and limit evidence."""
from __future__ import annotations
import ctypes as C
from ctypes import wintypes as W
import os
import subprocess
import hashlib

SIZE = C.c_size_t
HANDLE = W.HANDLE


class Memory(C.Structure):
    _fields_ = [('size', W.DWORD), ('load', W.DWORD)] + [(n, C.c_ulonglong) for n in (
        'total_phys', 'avail_phys', 'total_commit', 'avail_commit',
        'total_virtual', 'avail_virtual', 'extended')]


class Basic(C.Structure):
    _fields_ = [('process_time', C.c_int64), ('job_time', C.c_int64),
                ('flags', W.DWORD), ('min_working', SIZE), ('max_working', SIZE),
                ('active', W.DWORD), ('affinity', SIZE), ('priority', W.DWORD), ('scheduling', W.DWORD)]


class IO(C.Structure):
    _fields_ = [(n, C.c_ulonglong) for n in ('read_ops', 'write_ops', 'other_ops', 'read_bytes', 'write_bytes', 'other_bytes')]


class Extended(C.Structure):
    _fields_ = [('basic', Basic), ('io', IO)] + [(n, SIZE) for n in ('process_memory', 'job_memory', 'peak_process', 'peak_job')]


class Completion(C.Structure):
    _fields_ = [('key', C.c_void_p), ('port', HANDLE)]


class ThreadEntry(C.Structure):
    _fields_ = [('size', W.DWORD), ('usage', W.DWORD), ('thread_id', W.DWORD),
                ('process_id', W.DWORD), ('priority', C.c_int32), ('delta', C.c_int32), ('flags', W.DWORD)]


class Accounting(C.Structure):
    _fields_ = [(n, C.c_int64) for n in ('user_time', 'kernel_time', 'period_user_time', 'period_kernel_time')] + [
        (n, W.DWORD) for n in ('page_faults', 'total_processes', 'active_processes', 'terminated_processes')]


def api():
    if os.name != 'nt' or C.sizeof(C.c_void_p) != 8:
        raise ValueError('Use native 64-bit Windows Python for this measurement package')
    k = C.WinDLL('kernel32', use_last_error=True)
    definitions = {
        'CreateJobObjectW': ([C.c_void_p, W.LPCWSTR], HANDLE),
        'SetInformationJobObject': ([HANDLE, C.c_int, C.c_void_p, W.DWORD], W.BOOL),
        'QueryInformationJobObject': ([HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p], W.BOOL),
        'AssignProcessToJobObject': ([HANDLE, HANDLE], W.BOOL),
        'TerminateJobObject': ([HANDLE, W.UINT], W.BOOL),
        'CloseHandle': ([HANDLE], W.BOOL),
        'GlobalMemoryStatusEx': ([C.POINTER(Memory)], W.BOOL),
        'CreateIoCompletionPort': ([HANDLE, HANDLE, SIZE, W.DWORD], HANDLE),
        'GetQueuedCompletionStatus': ([HANDLE, C.POINTER(W.DWORD), C.POINTER(SIZE), C.POINTER(C.c_void_p), W.DWORD], W.BOOL),
        'CreateToolhelp32Snapshot': ([W.DWORD, W.DWORD], HANDLE),
        'Thread32First': ([HANDLE, C.POINTER(ThreadEntry)], W.BOOL),
        'Thread32Next': ([HANDLE, C.POINTER(ThreadEntry)], W.BOOL),
        'OpenThread': ([W.DWORD, W.BOOL, W.DWORD], HANDLE),
        'ResumeThread': ([HANDLE], W.DWORD),
        'OpenProcess': ([W.DWORD, W.BOOL, W.DWORD], HANDLE),
        'GetProcessTimes': ([HANDLE, C.POINTER(W.FILETIME), C.POINTER(W.FILETIME), C.POINTER(W.FILETIME), C.POINTER(W.FILETIME)], W.BOOL),
        'GetExitCodeProcess': ([HANDLE, C.POINTER(W.DWORD)], W.BOOL),
        'QueryFullProcessImageNameW': ([HANDLE, W.DWORD, W.LPWSTR, C.POINTER(W.DWORD)], W.BOOL),
        'GetCurrentProcess': ([], HANDLE),
        'GetProcessAffinityMask': ([HANDLE, C.POINTER(SIZE), C.POINTER(SIZE)], W.BOOL),
    }
    for name, (args, restype) in definitions.items():
        getattr(k, name).argtypes = args
        getattr(k, name).restype = restype
    return k


def check(value, operation):
    if not value:
        raise OSError(C.get_last_error(), operation)
    return value


def memory_available_mb():
    k = api()
    value = Memory()
    value.size = C.sizeof(value)
    check(k.GlobalMemoryStatusEx(C.byref(value)), 'GlobalMemoryStatusEx')
    return {'available_physical_mb': value.avail_phys / 1024**2,
            'available_commit_mb': value.avail_commit / 1024**2}


def process_identity(pid):
    if type(pid) is not int or pid <= 0:
        raise ValueError('Invalid saved process ID')
    k = api()
    handle = k.OpenProcess(0x1000, False, pid)
    if not handle:
        if C.get_last_error() == 87:
            return None
        raise ValueError('Process identity is uncertain; inspect it before recovery')
    try:
        code = W.DWORD()
        check(k.GetExitCodeProcess(handle, C.byref(code)), 'GetExitCodeProcess')
        if code.value != 259:
            return None
        times = [W.FILETIME() for _ in range(4)]
        check(k.GetProcessTimes(handle, *(C.byref(v) for v in times)), 'GetProcessTimes')
        text = C.create_unicode_buffer(32768)
        length = W.DWORD(len(text))
        check(k.QueryFullProcessImageNameW(handle, 0, text, C.byref(length)), 'QueryFullProcessImageNameW')
        # An opaque identity hash allows PID-reuse checks without storing a date.
        token = hashlib.sha256(str((times[0].dwHighDateTime << 32) | times[0].dwLowDateTime).encode()).hexdigest()
        return {'pid': pid, 'creation_token': token, 'image': text.value}
    finally:
        k.CloseHandle(handle)


def same_process_alive(saved):
    live = process_identity(saved['pid'])
    if live is None:
        return False
    if not saved.get('creation_token'):
        raise ValueError('Saved creation identity missing; recovery refused')
    return live['creation_token'] == saved['creation_token']


class WorkerProcess:
    def __init__(self, command, stdout, stderr, cwd, cpu=0, memory_bytes=8 * 1024**3):
        self.k = api()
        self.job = self.port = None
        self.process = None
        self.assigned = False
        self.events = []
        mask, system = SIZE(), SIZE()
        check(self.k.GetProcessAffinityMask(self.k.GetCurrentProcess(), C.byref(mask), C.byref(system)), 'GetProcessAffinityMask')
        if not 0 <= cpu < 64 or not mask.value & (1 << cpu):
            raise ValueError('CPU index not available to this Python process')
        try:
            self.job = check(self.k.CreateJobObjectW(None, None), 'CreateJobObjectW')
            limits = Extended()
            limits.basic.flags = 0x2000 | 0x10 | 0x200  # KILL_ON_CLOSE, affinity, JOB_MEMORY
            limits.basic.affinity = 1 << cpu
            limits.job_memory = memory_bytes
            check(self.k.SetInformationJobObject(self.job, 9, C.byref(limits), C.sizeof(limits)), 'SetInformationJobObject limits')
            self.port = check(self.k.CreateIoCompletionPort(HANDLE(-1), None, 0, 1), 'CreateIoCompletionPort')
            association = Completion(1, self.port)
            check(self.k.SetInformationJobObject(self.job, 7, C.byref(association), C.sizeof(association)), 'SetInformationJobObject completion')
            env = os.environ.copy()
            for name in ('OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
                env[name] = '1'
            self.process = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=stderr, env=env,
                                            creationflags=subprocess.CREATE_NO_WINDOW | 0x4)
            check(self.k.AssignProcessToJobObject(self.job, HANDLE(int(self.process._handle))), 'AssignProcessToJobObject')
            self.assigned = True
            self.identity = process_identity(self.process.pid)
            self._resume(self.process.pid)
        except BaseException:
            self.close()
            raise

    def _resume(self, pid):
        snapshot = self.k.CreateToolhelp32Snapshot(4, 0)
        if snapshot == HANDLE(-1).value:
            raise OSError(C.get_last_error(), 'CreateToolhelp32Snapshot')
        found = 0
        try:
            entry = ThreadEntry()
            entry.size = C.sizeof(entry)
            ok = self.k.Thread32First(snapshot, C.byref(entry))
            while ok:
                if entry.process_id == pid:
                    thread = check(self.k.OpenThread(2, False, entry.thread_id), 'OpenThread')
                    try:
                        if self.k.ResumeThread(thread) == 0xFFFFFFFF:
                            raise OSError(C.get_last_error(), 'ResumeThread')
                        found += 1
                    finally:
                        self.k.CloseHandle(thread)
                ok = self.k.Thread32Next(snapshot, C.byref(entry))
        finally:
            self.k.CloseHandle(snapshot)
        if not found:
            raise ValueError('Suspended worker thread not found; launch aborted')

    def poll(self):
        return self.process.poll()

    def sample(self):
        while True:
            message, key, value = W.DWORD(), SIZE(), C.c_void_p()
            ok = self.k.GetQueuedCompletionStatus(self.port, C.byref(message), C.byref(key), C.byref(value), 0)
            if not ok:
                if C.get_last_error() == 258:
                    break
                raise OSError(C.get_last_error(), 'GetQueuedCompletionStatus')
            if message.value in (9, 10):
                self.events.append({'message': message.value, 'kind': 'job_memory_limit', 'pid': value.value})
        limits = Extended()
        check(self.k.QueryInformationJobObject(self.job, 9, C.byref(limits), C.sizeof(limits), None), 'QueryInformationJobObject')
        accounting = Accounting()
        check(self.k.QueryInformationJobObject(self.job, 1, C.byref(accounting), C.sizeof(accounting), None), 'Query job accounting')
        return {'peak_job_private_commit_bytes': limits.peak_job,
                'declared_job_private_commit_bytes': limits.job_memory,
                'kernel_tree_cpu_seconds': (accounting.user_time + accounting.kernel_time) / 10000000,
                'active_kernel_tree_processes': accounting.active_processes,
                'memory_limit_events': list(self.events)}

    def close(self):
        try:
            if self.process is not None and self.process.poll() is None:
                if self.job and self.assigned:
                    if not self.k.TerminateJobObject(self.job, 0xE0000001):
                        self.process.kill()
                else:
                    self.process.kill()
            if self.process is not None:
                self.process.wait(timeout=10)
        finally:
            if self.job:
                self.k.CloseHandle(self.job)  # also releases remaining descendants
                self.job = None
            if self.port:
                self.k.CloseHandle(self.port)
                self.port = None
