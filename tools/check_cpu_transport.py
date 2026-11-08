"""Pure-Python CPU transport custody/recovery regressions; no SSH or Lean."""
import base64
from contextlib import redirect_stdout
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

import cpu_cfr as transport


def rejects(function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except (RuntimeError, subprocess.TimeoutExpired):
        return
    raise AssertionError('Unsafe transport action accepted')


def fixture(root):
    run='cfr-transport-fixture'
    path=root/'evidence/cpu'/run
    path.mkdir(parents=True)
    files={'inputs.tar.gz':b'Non-executed archive fixture', 'capture-controller.py':b'# capture fixture'}
    for name in transport.CONTROL_NAMES:
        files[name]=(transport.ROOT/'tools'/name).read_bytes()
    manifest=dict(run=run,compile_host='CPU',instance='cpu-02',project=None,zone=None,builder_profile=None,
        archive_sha256=transport.digest(files['inputs.tar.gz']),capture_controller_sha256=transport.digest(files['capture-controller.py']),
        execution_control_sha256={n:transport.digest(files[n]) for n in transport.CONTROL_NAMES},
        source_sha256={},dependencies=[],targets=['CorruptedFieldRecovery.Fixture'],audit=True,
        audit_path='checks/CaptureAudit.lean',audited_exports=['CorruptedFieldRecovery.fixture'])
    files['capture-manifest.json']=(json.dumps(manifest)+'\n').encode()
    for name,data in files.items():(path/name).write_bytes(data)
    owner=dict(status='ADMITTED',paper='P002',run=run,host='cpu-02',
        run_directory=transport.WORKER_ROOT+'/runs/'+run,campaign=transport.WORKER_ROOT+'/campaigns/fixture',
        admission_path=transport.WORKER_ROOT+'/admissions/fixture.json',
        capture_manifest_sha256=transport.digest(files['capture-manifest.json']),
        transport_sha256=manifest['execution_control_sha256']['cpu_cfr.py'],
        toolchain_sha256={'lean':'a'*64,'lake':'b'*64})
    admission=root/'admission-input.json';admission.write_text(json.dumps(owner))
    return run,path,manifest,admission,transport.digest(admission.read_bytes()),owner


def server_regression():
    if os.name != 'posix' or os.getuid() != 986:
        return 'native designated-worker fixture pending'
    with tempfile.TemporaryDirectory(prefix='cfr-transport-server-fixture-') as directory:
        root=Path(directory);run_id='cfr-server-fixture';run=root/'runs'/run_id;campaign=root/'campaign'
        for path in [run.parent,campaign/'packages',campaign/'mathlib-cache',root/'tool',root/'admissions']:
            path.mkdir(parents=True)
        value=dict(host='cpu-02',uid=986,worker_name='quantyra-worker',
            cgroup='0::/user.slice/user-986.slice/fixture.scope',free_bytes=30*2**30,
            cpu_max='200000 100000',memory_high=4*2**30,memory_max=5*2**30,swap_max=0,
            tasks_max=256,memory_current=2**20,events=dict(high=0,max=0,oom=0,oom_kill=0))
        controls={n:(transport.ROOT/'tools'/n).read_bytes() for n in transport.CONTROL_NAMES}
        # All host admission and lease values below are synthetic fixture data.
        # The external runner process is mocked; no real compiler is invoked.
        controls['cpu_cfr_runner.py']+=('\nROOT = Path('+repr(str(root))+')\n'
            'def observe(): return '+repr(value)+'\n'
            '_FixtureGuard = ResourceGuard\n'
            'def ResourceGuard(host): return _FixtureGuard(host, read=observe)\n'
            'def compiler_processes(): return []\n'
            'def compiler_lease(path): return __import__("contextlib").nullcontext()\n').encode()
        data={'inputs.tar.gz':b'Digest-only fixture; never extracted',
              'capture-controller.py':b'# fixture',**controls}
        manifest=dict(run=run_id,compile_host='CPU',instance='cpu-02',project=None,zone=None,builder_profile=None,
            archive_sha256=transport.digest(data['inputs.tar.gz']),capture_controller_sha256=transport.digest(data['capture-controller.py']),
            execution_control_sha256={n:transport.digest(b) for n,b in controls.items()},
            source_sha256={},dependencies=[],targets=['CorruptedFieldRecovery.Fixture'],
            audit=True,audit_path='checks/CaptureAudit.lean',audited_exports=['CorruptedFieldRecovery.fixture'],
            utf8_no_bom_verified=True,lean_toolchain='leanprover/lean4:v4.30.0')
        data['capture-manifest.json']=json.dumps(manifest).encode()
        provenance=root/'dependency-origin.json';provenance.write_text(json.dumps({'origin':'fresh-public-pinned','packages':{}}))
        for name in ['lean','lake']:(root/'tool'/name).write_bytes(b'Non-executable identity fixture')
        admission_path=root/'admissions/fixture.json'
        owner=dict(status='ADMITTED',paper='P002',host='cpu-02',run=run_id,run_directory=str(run),
            campaign=str(campaign),admission_path=str(admission_path),compiler_custody_reference='fixture only',
            capture_manifest_sha256=transport.digest(data['capture-manifest.json']),archive_sha256=manifest['archive_sha256'],
            runner_sha256=manifest['execution_control_sha256']['cpu_cfr_runner.py'],
            engine_sha256=manifest['execution_control_sha256']['gcp_cfr_runner.py'],
            transport_sha256=manifest['execution_control_sha256']['cpu_cfr.py'],
            toolchain_bin=str(root/'tool'),toolchain_sha256={n:transport.digest((root/'tool'/n).read_bytes()) for n in ['lean','lake']},
            dependency_provenance_path=str(provenance),dependency_provenance_sha256=transport.digest(provenance.read_bytes()),
            lease_file=str(root/'fixture.lock'))
        admission_path.write_text(json.dumps(owner))
        payload=dict(run=run_id,host='cpu-02',remote_run=str(run),campaign=str(campaign),
            manifest=base64.b64encode(data['capture-manifest.json']).decode(),
            manifest_sha256=owner['capture_manifest_sha256'],admission_path=str(admission_path),
            admission_sha256=transport.digest(admission_path.read_bytes()),claim='fixture-custody',
            controls={n:base64.b64encode(b).decode() for n,b in controls.items()})
        def invoke(operation,**extra):
            request=dict(payload,operation=operation,**extra)
            script=transport.REMOTE_AGENT.replace('P = PAYLOAD','P = '+repr(request),1)
            output=io.StringIO()
            with redirect_stdout(output): exec(compile(script,'<synthetic-remote-agent>','exec'),{})
            return json.loads(output.getvalue())
        with patch.dict(__import__('sys').modules,{}):
            ready=invoke('preflight');assert ready['ok'] and not run.exists()
            files={n:base64.b64encode(b).decode() for n,b in data.items()}
            with patch.object(subprocess,'Popen',return_value=SimpleNamespace(pid=987654321,wait=lambda timeout:3)) as process:
                result=invoke('stage',files=files)
                assert result['ok'] and result['result']['completion']['exit_code']==3,result
                assert process.call_count==1
                again=invoke('stage',files=files)
                assert not again['ok'] and process.call_count==1
            assert invoke('observe')['result']['handles']==[]
            collected=invoke('collect')
            assert collected['ok'] and collected['result']['terminal'] is None
            for item in collected['result']['files'].values():
                assert transport.digest(base64.b64decode(item['content']))==item['sha256']
    return 'native worker server fixture passed; admission/lease/processes synthetic'


def main():
    for bad in ['../x','cfr-foo;touch-x','cfr-foo/bar','cfr-foo\\bar']:
        rejects(transport.packet,bad)
    assert not any(transport.evidence_name(n) for n in ['../../secret','C:secret','logs/../../token','credentials.txt'])
    with tempfile.TemporaryDirectory() as directory:
        root=Path(directory);run,path,manifest,admission,sha,owner=fixture(root);calls=[]
        def denied(host,name,payload,**kwargs):
            calls.append(payload)
            assert 'files' not in payload and payload['operation']=='preflight'
            raise RuntimeError('fixture root-space/admission failure')
        with patch.object(transport,'ROOT',root):
            rejects(transport.submit,run,admission,sha,call=denied)
            assert len(calls)==1 and not (path/'submission-attempt.json').exists()
            rejects(transport.submit,run,admission,'0'*64,call=denied)
            assert len(calls)==1

    with tempfile.TemporaryDirectory() as directory:
        root=Path(directory);run,path,manifest,admission,sha,owner=fixture(root);calls=[]
        def uncertain(host,name,payload,**kwargs):
            calls.append(payload)
            if payload['operation']=='preflight':
                assert 'files' not in payload
                return {'status':'PREFLIGHT_PASS_NOT_LAUNCHED'}
            assert payload['operation']=='stage' and set(payload['files'])=={
                'capture-manifest.json','inputs.tar.gz','capture-controller.py',*transport.CONTROL_NAMES}
            raise subprocess.TimeoutExpired('fixture SSH loss',1)
        with patch.object(transport,'ROOT',root):
            rejects(transport.submit,run,admission,sha,call=uncertain)
            assert (path/'submission-attempt.json').is_file() and len(calls)==2
            rejects(transport.submit,run,admission,sha,call=uncertain)
            assert len(calls)==2  # Lost observation never becomes an automatic duplicate.
        spec=importlib.util.spec_from_file_location('captured_cpu_transport_fixture',path/'cpu_cfr.py')
        captured=importlib.util.module_from_spec(spec);spec.loader.exec_module(captured)
        assert captured.ROOT==root  # Recovery uses the retained controller after current tools change.
        def active(host,name,payload,**kwargs):
            assert 'files' not in payload
            return {'status':'ACTIVE','handles':[{'pid':7,'start_ticks':'fixture','role':'runner'}]}
        assert captured.observe_or_collect(run,call=active)['status']=='ACTIVE'
        rejects(captured.observe_or_collect,run,collect=True,call=active)

        log=b'Synthetic build log, no compiler executed\n'
        body='theorem CorruptedFieldRecovery.fixture : True\n'
        types=json.dumps({'CorruptedFieldRecovery.fixture':{'emitted_type':body,'sha256':transport.digest(body.encode())}}).encode()
        logs={'logs/build.stdout.txt':log,'logs/build.stderr.txt':b'',
              'logs/audit.stdout.txt':b'Synthetic audit log','logs/audit.stderr.txt':b''}
        terminal=dict(run=run,compile_host='CPU',instance='cpu-02',worker_uid=986,status='passed',
            source_sha256=manifest['source_sha256'],dependencies=[],admission_sha256=sha,
            runner_sha256=manifest['execution_control_sha256']['cpu_cfr_runner.py'],
            engine_sha256=manifest['execution_control_sha256']['gcp_cfr_runner.py'],
            transport_sha256=manifest['execution_control_sha256']['cpu_cfr.py'],
            source_and_dependencies_verified_before=True,source_and_dependencies_verified_after=True,
            toolchain_binary_sha256=owner['toolchain_sha256'],lean_commit_verified='d024af099ca4bf2c86f649261ebf59565dc8c622',
            stage_outcomes=[dict(stage='build',command=['lake','build',*manifest['targets']],exit_code=0,timed_out=False),
                            dict(stage='audit',command=['lake','env','lean',manifest['audit_path']],exit_code=0,timed_out=False)],
            log_sha256={name:transport.digest(raw) for name,raw in logs.items()},
            audited_declarations=manifest['audited_exports'],reported_axioms=[],
            type_axiom_audit={'emitted_types_sha256':transport.digest(types),
                             'type_block_sha256':{'CorruptedFieldRecovery.fixture':transport.digest(body.encode())}})
        def result(term=terminal,extra=None):
            data={'terminal-receipt.json':json.dumps(term).encode(),'logs/emitted-types.json':types,**logs}
            if extra:data.update(extra)
            return dict(status='TERMINAL',handles=[],terminal=term,
                files={name:{'content':base64.b64encode(raw).decode(),'sha256':transport.digest(raw)} for name,raw in data.items()})
        collected=captured.observe_or_collect(run,collect=True,call=lambda *a,**k:result())
        assert collected['semantic_acceptance'] is False
        receipt=json.loads((Path(collected['collection'])/'collection.json').read_text())
        assert receipt['semantic_acceptance'] is False and receipt['files']['logs/build.stdout.txt']==transport.digest(log)
        rejects(captured.observe_or_collect,run,collect=True,call=lambda *a,**k:result(extra={'C:secret':b'unsafe'}))
        for key,value in [('source_sha256',{'wrong':'0'*64}),('runner_sha256','0'*64),('reported_axioms',['sorryAx']),
                          ('source_and_dependencies_verified_after',False),('lean_commit_verified','wrong')]:
            rejects(captured.observe_or_collect,run,collect=True,call=lambda *a,**k:result(dict(terminal,**{key:value})))
        (path/'inputs.tar.gz').write_bytes(b'changed source')
        rejects(captured.observe_or_collect,run,call=active)
    # SSH configuration itself is fixed and never disables host authentication.
    answer=type('Answer',(),{'returncode':0,'stdout':'{"ok":true,"result":{"status":"fixture"}}','stderr':''})()
    with patch.object(transport.subprocess,'run',return_value=answer) as process:
        assert transport.rpc('cpu-02','cfr-fixture',{'operation':'observe'})['status']=='fixture'
        command=process.call_args.args[0]
        assert 'StrictHostKeyChecking=yes' in command and 'BatchMode=yes' in command and 'cpu-02' in command
        assert command[command.index('-l')+1]=='quantyra-worker'
        assert command[-1]=='python3 - cfr-fixture observe'
    server=server_regression()
    print('PASS: no proof upload before admission, immutable packet/control checks, SSH-loss journal/no duplicate, captured-controller recovery, active-handle hold, closed log/type/source/control/axiom verification; no SSH/Lean; '+server)


if __name__=='__main__': main()
