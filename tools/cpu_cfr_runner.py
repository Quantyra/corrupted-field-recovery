"""Admitted Linux CPU entry point; no provisioning, transfer or implicit admission.

Usage: python3 cpu_cfr_runner.py RUN CAMPAIGN ADMISSION ADMISSION_SHA256
The owner-pinned admission binds this run, both runner files, toolchain binaries,
fresh public dependency provenance and an existing host-wide compiler lease.
"""
from contextlib import contextmanager
import json
import os
from pathlib import Path
import re
import shutil
import signal
import socket
import subprocess
import sys
import time

import gcp_cfr_runner as engine

ROOT = Path('/srv/kuzuryu-cloud/quantyra')
CGROUP = Path('/sys/fs/cgroup/user.slice/user-986.slice')
MIN_FREE = 20 * 2**30
MAX_HIGH = 4 * 2**30
MAX_MEMORY = 5 * 2**30
MAX_SECONDS = 4 * 3600
EVENTS = ('high', 'max', 'oom', 'oom_kill')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def validate_observation(value, host):
    require(host in {'cpu-01', 'cpu-02'} and value['host'] == host, 'Wrong CPU host')
    require(value['uid'] == 986 and value['worker_name'] == 'quantyra-worker', 'Wrong worker identity')
    require(value['cgroup'].startswith('0::/user.slice/user-986.slice/'), 'Wrong worker cgroup')
    require(value['free_bytes'] >= MIN_FREE, 'Root free-space guard failed')
    quota, period = value['cpu_max'].split()
    require(quota != 'max' and 0 < int(quota) <= 2 * int(period) and int(period) > 0, 'CPU quota guard failed')
    require(0 < value['memory_high'] <= MAX_HIGH, 'MemoryHigh guard failed')
    require(value['memory_high'] <= value['memory_max'] <= MAX_MEMORY, 'MemoryMax guard failed')
    require(value['swap_max'] == 0 and 0 < value['tasks_max'] <= 256, 'Swap/task guard failed')
    require(value['memory_current'] < value['memory_high'], 'Worker is already under memory pressure')
    require(all(isinstance(value['events'].get(k), int) and value['events'][k] >= 0 for k in EVENTS),
            'Incomplete memory-event observation')


def observe():
    import pwd
    def number(name):
        return int((CGROUP/name).read_text().strip())
    return dict(host=socket.gethostname().split('.')[0], uid=os.getuid(),
                worker_name=pwd.getpwuid(os.getuid()).pw_name,
                cgroup=Path('/proc/self/cgroup').read_text().strip(),
                free_bytes=shutil.disk_usage('/').free,
                cpu_max=(CGROUP/'cpu.max').read_text().strip(),
                memory_high=number('memory.high'), memory_max=number('memory.max'),
                swap_max=number('memory.swap.max'), tasks_max=number('pids.max'),
                memory_current=number('memory.current'),
                events={k:int(v) for k,v in (line.split() for line in (CGROUP/'memory.events').read_text().splitlines())})


def compiler_processes():
    text = subprocess.check_output(['ps', '-eo', 'pid,comm'], text=True)
    return [line.strip() for line in text.splitlines()[1:]
            if len(line.split()) == 2 and line.split()[1] in {'lean', 'lake'}]


def owned_path(value):
    path = Path(value)
    require(path.is_absolute(), 'Admission paths must be absolute')
    path = path.resolve()
    require(path != ROOT and path.is_relative_to(ROOT), 'Path escapes admitted worker root')
    return path


def owned_by_worker(path):
    return path.stat().st_uid == 986


def validate_packet(run, campaign, admission, manifest):
    require(admission['paper'] == 'P002', 'Wrong paper admission')
    require(admission.get('status') == 'ADMITTED', 'Owner admission is not established')
    host = admission['host']
    require(host in {'cpu-01', 'cpu-02'} and manifest['instance'] == host, 'Capture/admission host mismatch')
    require(manifest['compile_host'] == 'CPU' and
            all(manifest.get(k) is None for k in ('project', 'zone', 'builder_profile')),
            'CPU packet must not impersonate a GCP builder')
    require(manifest['run'] == run.name == admission['run'] == os.environ.get('CFR_CPU_RUN'), 'Run identity mismatch')
    require(admission['capture_manifest_sha256'] == engine.digest(run/'capture-manifest.json'), 'Capture manifest changed')
    require(admission['archive_sha256'] == manifest['archive_sha256'] == engine.digest(run/'inputs.tar.gz'), 'Captured archive changed')
    require(manifest['utf8_no_bom_verified'] and manifest['lean_toolchain'] == 'leanprover/lean4:v4.30.0', 'Encoding/toolchain mismatch')
    require(manifest['audit'] and manifest['audited_exports'] and manifest['targets'], 'Explicit target/type/axiom audit required')
    require(all(re.fullmatch(r'CorruptedFieldRecovery(?:\.[A-Za-z_][A-Za-z0-9_\']*)*', name)
                for name in manifest['targets'] + manifest['audited_exports']), 'Invalid owned target/export')
    require(owned_path(admission['campaign']) == campaign, 'Campaign binding changed')
    require(run != campaign and not run.is_relative_to(campaign) and not campaign.is_relative_to(run), 'Run/campaign overlap')
    require(admission.get('compiler_custody_reference'), 'Compiler custody reference required')
    require(admission['runner_sha256'] == engine.digest(Path(__file__)), 'CPU runner changed')
    require(admission['engine_sha256'] == engine.digest(Path(engine.__file__)), 'Shared stage engine changed')
    require(manifest['execution_control_sha256'] == {
        'cpu_cfr_runner.py':admission['runner_sha256'], 'gcp_cfr_runner.py':admission['engine_sha256']},
        'Execution controls differ from captured offer')
    tool = owned_path(admission['toolchain_bin'])
    require(set(admission['toolchain_sha256']) == {'lean', 'lake'}, 'Both executable pins required')
    for name, expected in admission['toolchain_sha256'].items():
        require(expected == engine.digest(tool/name), 'Toolchain executable changed: '+name)
    # CPU admission requires a separately qualified private, fresh-public workspace.
    # Never bootstrap this route by copying historical VM/build/cache archives.
    require((campaign/'packages').is_dir() and (campaign/'mathlib-cache').is_dir(), 'Qualified CPU dependencies/cache absent')
    provenance = owned_path(admission['dependency_provenance_path'])
    require(engine.digest(provenance) == admission['dependency_provenance_sha256'], 'Dependency provenance changed')
    origins = json.loads(provenance.read_text())
    require(origins['origin'] == 'fresh-public-pinned', 'CPU dependency origin not qualified')
    require(origins['packages'] == {p['name']:p['rev'] for p in manifest['dependencies']}, 'Dependency provenance pins differ')
    require(owned_by_worker(run) and owned_by_worker(campaign), 'Run/campaign not worker-owned')
    return tool, owned_path(admission['lease_file'])


@contextmanager
def compiler_lease(path):
    import fcntl
    # Owner establishes the shared compiler lease; never create an unrelated lock.
    require(path.is_file(), 'Owner-established compiler lease missing')
    with path.open('r+') as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError('Compiler lease is already held') from exc
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


class ResourceGuard:
    def __init__(self, host, read=observe, clock=time.monotonic):
        self.host, self.read, self.clock = host, read, clock
        self.started = clock()
        self.baseline = read()
        validate_observation(self.baseline, host)
        self.summary = dict(samples=0, minimum_root_free_bytes=self.baseline['free_bytes'],
                            maximum_memory_bytes=self.baseline['memory_current'], baseline_events=self.baseline['events'])

    def check(self):
        value = self.read()
        validate_observation(value, self.host)
        require(self.clock() - self.started < MAX_SECONDS, 'Total CPU run timeout')
        for key in ('cpu_max', 'memory_high', 'memory_max', 'swap_max', 'tasks_max'):
            require(value[key] == self.baseline[key], 'Resource binding changed: '+key)
        require(all(value['events'][key] == self.baseline['events'][key] for key in EVENTS),
                'Memory pressure/hard-cap/OOM event or counter reset')
        self.summary.update(samples=self.summary['samples']+1,
            minimum_root_free_bytes=min(self.summary['minimum_root_free_bytes'], value['free_bytes']),
            maximum_memory_bytes=max(self.summary['maximum_memory_bytes'], value['memory_current']),
            last_events=value['events'])

    def wait(self, process, timeout):
        start = self.clock()
        while True:
            self.check()
            code = process.poll()
            if code is not None:
                return code
            if self.clock() - start >= timeout:
                raise subprocess.TimeoutExpired(process.args, timeout)
            time.sleep(0.01)


def main():
    require(sys.platform == 'linux' and __debug__, 'CPU execution requires Linux with Python assertions enabled')
    require(os.getuid() == 986, 'CPU execution requires the designated worker UID')
    require(len(sys.argv) == 5, __doc__)
    run, campaign = owned_path(sys.argv[1]), owned_path(sys.argv[2])
    admission_path, expected = owned_path(sys.argv[3]), sys.argv[4]
    require(engine.digest(admission_path) == expected, 'Owner admission digest mismatch')
    admission = json.loads(admission_path.read_text())
    manifest = json.loads((run/'capture-manifest.json').read_text())
    guard = ResourceGuard(admission['host'])
    tool, lease = validate_packet(run, campaign, admission, manifest)
    require(not (run/'terminal-receipt.json').exists() and not (run/'immutable-source').exists(), 'Run already attempted; collect instead of restarting')
    with compiler_lease(lease):
        require(not compiler_processes(), 'Another Lean/Lake workload is active')
        guard.check()
        # Process-local limits only: no host/cgroup configuration writes.
        os.environ.update(LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', LAKE_JOBS='2',
                          GIT_TERMINAL_PROMPT='0', GIT_ASKPASS='/bin/false', SSH_ASKPASS='/bin/false')
        handled = (signal.SIGALRM, signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
        original_handlers = {number:signal.getsignal(number) for number in handled}
        def stop(signum, frame):
            reason = 'Total CPU run timeout' if signum == signal.SIGALRM else 'CPU run cancelled by signal '+str(signum)
            raise RuntimeError(reason)
        for number in handled:
            signal.signal(number, stop)
        signal.alarm(max(1, int(MAX_SECONDS - (time.monotonic() - guard.started))))
        try:
            return engine.execute_captured(run, campaign, manifest,
                dict(compile_host='CPU', instance=admission['host'], worker_uid=986,
                     compiler_custody_reference=admission['compiler_custody_reference'],
                     admission_sha256=expected, runner_sha256=admission['runner_sha256'],
                     engine_sha256=admission['engine_sha256'], resource_observation=guard.summary),
                toolchain_bin=tool, resource_guard=guard.check, wait_process=guard.wait)
        finally:
            signal.alarm(0)
            for number, handler in original_handlers.items():
                signal.signal(number, handler)


if __name__ == '__main__':
    raise SystemExit(main())
