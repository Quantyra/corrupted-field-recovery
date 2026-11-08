"""CPU admission/resource/receipt regressions; no Lean, Lake, SSH or live host."""
import copy
from contextlib import ExitStack
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tarfile
from types import SimpleNamespace
from unittest.mock import patch

import cpu_cfr_runner as cpu
import gcp_cfr_runner as engine


def observation():
    return dict(host='cpu-02', uid=986, worker_name='quantyra-worker',
                cgroup='0::/user.slice/user-986.slice/session-1.scope',
                free_bytes=cpu.MIN_FREE, cpu_max='200000 100000',
                memory_high=cpu.MAX_HIGH, memory_max=cpu.MAX_MEMORY,
                swap_max=0, tasks_max=256, memory_current=2**30,
                events=dict(high=0, max=0, oom=0, oom_kill=0))


def rejects(function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except (RuntimeError, subprocess.TimeoutExpired):
        return
    raise AssertionError('A failed CPU admission/resource condition was accepted')


def main():
    base = observation()
    cpu.validate_observation(base, 'cpu-02')
    bad_fields = dict(host='cpu-01', uid=1000, worker_name='cpu-02',
        cgroup='0::/user.slice/user-1000.slice/session-1.scope', free_bytes=cpu.MIN_FREE-1,
        cpu_max='max 100000', memory_high=cpu.MAX_HIGH+1, memory_max=cpu.MAX_MEMORY+1,
        swap_max=1, tasks_max=257, memory_current=cpu.MAX_HIGH)
    for key, value in bad_fields.items():
        bad = dict(base, **{key:value})
        rejects(cpu.validate_observation, bad, 'cpu-02')
    for event in cpu.EVENTS:
        current = copy.deepcopy(base)
        guard = cpu.ResourceGuard('cpu-02', read=lambda:copy.deepcopy(current), clock=lambda:0)
        guard.check()
        current['events'][event] += 1
        rejects(guard.check)
    current = copy.deepcopy(base)
    guard = cpu.ResourceGuard('cpu-02', read=lambda:copy.deepcopy(current), clock=lambda:0)
    current['cpu_max'] = '100000 100000'  # Even a stricter unrecorded binding change stops the run.
    rejects(guard.check)
    clock = [0]
    guard = cpu.ResourceGuard('cpu-02', read=observation, clock=lambda:clock[0])
    clock[0] = cpu.MAX_SECONDS
    rejects(guard.check)

    class FakeProcess:
        args = ['fixture-only']
        def poll(self):
            return 0
    guard = cpu.ResourceGuard('cpu-02', read=observation, clock=lambda:0)
    assert guard.wait(FakeProcess(), 1) == 0
    with patch.object(cpu.sys, 'platform', 'win32'):
        rejects(cpu.main)
    with patch.object(engine.sys, 'platform', 'win32'):
        rejects(engine.execute_captured, None, None, None, None)

    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        run, campaign, tool = root/'run', root/'campaign', root/'toolchain'
        for path in [run, campaign/'packages', campaign/'mathlib-cache', tool]:
            path.mkdir(parents=True)
        for name in ['lean', 'lake']:
            (tool/name).write_bytes(b'Non-executable hash fixture only')
        provenance = root/'provenance.json'
        provenance.write_text(json.dumps({'origin':'fresh-public-pinned', 'packages':{}}))
        (run/'inputs.tar.gz').write_bytes(b'Archive digest fixture only')
        manifest = dict(run='run', compile_host='CPU', instance='cpu-02', project=None, zone=None,
            builder_profile=None, archive_sha256=engine.digest(run/'inputs.tar.gz'), utf8_no_bom_verified=True,
            lean_toolchain='leanprover/lean4:v4.30.0', audit=True, targets=['CorruptedFieldRecovery.Fixture'],
            audited_exports=['CorruptedFieldRecovery.fixture'], dependencies=[])
        (run/'capture-manifest.json').write_text(json.dumps(manifest))
        manifest['execution_control_sha256'] = {
            'cpu_cfr_runner.py':engine.digest(Path(cpu.__file__)),
            'gcp_cfr_runner.py':engine.digest(Path(engine.__file__)),
            'cpu_cfr.py':hashlib.sha256(b'fixture transport').hexdigest()}
        (run/'cpu_cfr.py').write_bytes(b'fixture transport')
        (run/'capture-manifest.json').write_text(json.dumps(manifest))
        admission = dict(paper='P002', status='ADMITTED', host='cpu-02', run='run', campaign=str(campaign), run_directory=str(run),
            admission_path=str(root/'owner-admission.json'),
            capture_manifest_sha256=engine.digest(run/'capture-manifest.json'), archive_sha256=manifest['archive_sha256'],
            compiler_custody_reference='fixture only', runner_sha256=engine.digest(Path(cpu.__file__)),
            engine_sha256=engine.digest(Path(engine.__file__)), toolchain_bin=str(tool),
            transport_sha256=manifest['execution_control_sha256']['cpu_cfr.py'],
            toolchain_sha256={name:engine.digest(tool/name) for name in ['lean', 'lake']},
            dependency_provenance_path=str(provenance), dependency_provenance_sha256=engine.digest(provenance),
            lease_file=str(root/'compiler.lock'))
        with patch.object(cpu, 'ROOT', root), patch.object(cpu, 'owned_by_worker', return_value=True), \
             patch.dict(cpu.os.environ, {'CFR_CPU_RUN':'run'}), patch.object(engine.subprocess, 'Popen') as popen:
            assert cpu.validate_packet(run, campaign, admission, manifest) == (tool, root/'compiler.lock')
            for key, value in [('status','PENDING'), ('paper','P001'), ('host','cpu-01'),
                               ('capture_manifest_sha256','0'*64), ('archive_sha256','0'*64),
                               ('runner_sha256','0'*64), ('engine_sha256','0'*64),
                               ('dependency_provenance_sha256','0'*64)]:
                rejects(cpu.validate_packet, run, campaign, dict(admission, **{key:value}), manifest)
            rejects(cpu.validate_packet, run, campaign, admission, dict(manifest, compile_host='GCP'))
            rejects(cpu.validate_packet, run, campaign, admission, dict(manifest, audit=False))
            rejects(cpu.validate_packet, run, campaign, admission, dict(manifest, targets=['--help']))
            rejects(cpu.owned_path, str(root.parent/'outside'))
            (tool/'lean').write_bytes(b'Changed binary fixture')
            rejects(cpu.validate_packet, run, campaign, admission, manifest)
            popen.assert_not_called()
        # Exercise lock lifetime and contention without acquiring a real host/compiler lease.
        lease = root/'fixture.lock'
        lease.write_text('fixture only')
        calls = []
        fake = SimpleNamespace(LOCK_EX=1, LOCK_NB=2, LOCK_UN=4,
                               flock=lambda handle, mode:calls.append(mode))
        with patch.dict(sys.modules, {'fcntl':fake}):
            with cpu.compiler_lease(lease):
                assert calls == [3]
            assert calls == [3, 4]
        def held(handle, mode):
            raise BlockingIOError('fixture contention')
        fake.flock = held
        with patch.dict(sys.modules, {'fcntl':fake}):
            rejects(lambda:cpu.compiler_lease(lease).__enter__())

    # A CPU-labelled packet cannot bypass the unchanged GCP entry-point guard.
    with tempfile.TemporaryDirectory() as directory:
        run = Path(directory)/'cfr-fixture'
        run.mkdir()
        (run/'capture-manifest.json').write_text(json.dumps({'run':run.name, 'compile_host':'CPU'}))
        with patch.object(engine.sys, 'platform', 'linux'), \
             patch.object(engine.sys, 'argv', ['runner', str(run), str(Path(directory)/'campaign')]), \
             patch.dict(engine.os.environ, {'CFR_GCP_RUN':run.name}), \
             patch.object(engine, 'execute_captured') as execute:
            try:
                engine.main()
            except AssertionError:
                pass
            else:
                raise AssertionError('GCP entry point accepted a CPU packet')
            execute.assert_not_called()

    # Failure before any external process still produces a failed shared-stage receipt.
    with tempfile.TemporaryDirectory() as directory:
        run = Path(directory)/'run'
        run.mkdir()
        (run/'inputs.tar.gz').write_bytes(b'fixture archive identity only')
        manifest = dict(run='run', utf8_no_bom_verified=True, lean_toolchain='leanprover/lean4:v4.30.0',
                        archive_sha256=engine.digest(run/'inputs.tar.gz'), source_sha256={}, dependencies=[])
        def fail_guard():
            raise RuntimeError('fixture admission/resource rejection')
        with patch.object(engine.sys, 'platform', 'linux'), patch.object(engine.subprocess, 'Popen') as popen:
            rejects(engine.execute_captured, run, Path(directory)/'campaign', manifest,
                    {'compile_host':'CPU', 'instance':'cpu-02'}, resource_guard=fail_guard)
            popen.assert_not_called()
        receipt = json.loads((run/'terminal-receipt.json').read_text())
        assert receipt['status'] == 'failed' and receipt['compile_host'] == 'CPU'
        assert receipt['stage_outcomes'] == [] and 'fixture admission' in receipt['failure']

    # A running-stage resource fault must stop its own group and retain closed log hashes.
    for timeout in [False, True]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            run, campaign, tool = root/'run', root/'campaign', root/'tool'
            for path in [run, campaign/'packages', campaign/'mathlib-cache', tool]:
                path.mkdir(parents=True)
            for name in ['lean','lake']:
                (tool/name).write_bytes(b'Identity fixture; never executed')
            data = b'-- fixture, not a proof\n'
            with tarfile.open(run/'inputs.tar.gz', 'w:gz') as archive:
                info = tarfile.TarInfo('CorruptedFieldRecovery/Fixture.lean')
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
            manifest = dict(run='run', utf8_no_bom_verified=True, lean_toolchain='leanprover/lean4:v4.30.0',
                archive_sha256=engine.digest(run/'inputs.tar.gz'),
                source_sha256={'CorruptedFieldRecovery/Fixture.lean':hashlib.sha256(data).hexdigest()}, dependencies=[])
            class StageProcess:
                pid = -1
                args = ['Never executed']
                def wait(self, timeout=None):
                    return 0
            def fail_wait(process, seconds):
                if timeout:
                    raise subprocess.TimeoutExpired(process.args, seconds)
                raise RuntimeError('fixture memory.high event')
            # Windows may lack symlink privilege. Model only this fixture link;
            # actual Linux filesystem/toolchain qualification remains outstanding.
            link = campaign/'source/.lake/packages'
            resolve = Path.resolve
            def fixture_resolve(path, *args, **kwargs):
                return resolve(campaign/'packages') if path == link else resolve(path, *args, **kwargs)
            def fixture_link(path, target, **kwargs):
                assert path == link and target == campaign/'packages'
                path.mkdir()
            with ExitStack() as filesystem, patch.object(engine.sys, 'platform', 'linux'), \
                 patch.object(engine.subprocess, 'Popen', return_value=StageProcess()) as popen, \
                 patch.object(engine.os, 'killpg', create=True) as kill:
                if os.name == 'nt':
                    filesystem.enter_context(patch.object(Path, 'resolve', fixture_resolve))
                    filesystem.enter_context(patch.object(Path, 'symlink_to', fixture_link))
                rejects(engine.execute_captured, run, campaign, manifest,
                    {'compile_host':'CPU', 'instance':'cpu-02'}, toolchain_bin=tool,
                    wait_process=fail_wait, resource_guard=lambda:None)
                assert popen.call_count == 1 and kill.call_count == 1
            receipt = json.loads((run/'terminal-receipt.json').read_text())
            stage = receipt['stage_outcomes'][0]
            assert receipt['status'] == 'failed' and stage['stage'] == 'lean-version'
            assert stage['exit_code'] == (124 if timeout else 125) and stage['timed_out'] == timeout
            assert len(receipt['log_sha256']) == 2
            for name, digest in receipt['log_sha256'].items():
                assert engine.digest(run/name) == digest

    # Resource faults can arrive after a process exits; do not mask them with ESRCH.
    class EndedProcess:
        pid = -1
        def wait(self, timeout=None):
            return 0
    with patch.object(engine.os, 'killpg', side_effect=ProcessLookupError(), create=True):
        engine.terminate_process_group(EndedProcess())
    print('PASS: CPU admission/source/control/toolchain bindings, lease contention/lifetime, resource stops, Windows/GCP rejection, stopped-stage failure/log hashes; no compiler/SSH')


if __name__ == '__main__':
    main()
