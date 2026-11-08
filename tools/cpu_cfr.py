"""Owner-bound CPU dispatch, observation and closed-log collection; never local Lean."""
import argparse
import base64
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import uuid

_FILE = Path(__file__).resolve()
ROOT = (_FILE.parents[3] if _FILE.parent.parent.name == 'cpu' and _FILE.parent.parent.parent.name == 'evidence'
        else _FILE.parents[1])
WORKER_ROOT = '/srv/kuzuryu-cloud/quantyra'
ALIASES = {'cpu-01':'cpu-01', 'cpu-02':'cpu-02'}
CONTROL_NAMES = ('cpu_cfr_runner.py', 'gcp_cfr_runner.py', 'cpu_cfr.py')
MAX_BYTES = 64 * 2**20
ROOT_EVIDENCE = {'launch-request.json','processes.json','completion.json','terminal-receipt.json',
                 'runner.stdout.txt','runner.stderr.txt','current-stage'}


def evidence_name(name):
    return name in ROOT_EVIDENCE or name == 'logs/emitted-types.json' or bool(re.fullmatch(
        r'logs/(?:lean-version|lake-version|dependency-cache|dependency-cache-incremental|build|audit)\.(?:stdout|stderr)\.txt',name))


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def write_new(path, value):
    with path.open('x', encoding='utf-8', newline='\n') as output:
        json.dump(value, output, indent=2)
        output.write('\n')


# Runs through python stdin. No shell receives paths, source, credentials or JSON.
# The sole command arguments are a validated run ID and a fixed operation name.
REMOTE_AGENT = r'''
import base64,hashlib,importlib.util,json,os,pathlib,subprocess,sys,time,types
from datetime import datetime,timezone
P = PAYLOAD
def sha(b): return hashlib.sha256(b).hexdigest()
def need(ok, message):
 if not ok: raise RuntimeError(message)
def stamp(): return datetime.now(timezone.utc).isoformat()
def load_controls(directory=None):
 global cpu,engine
 for filename in ('gcp_cfr_runner.py','cpu_cfr_runner.py'):
  name=filename[:-3]
  if directory is None:
   m=types.ModuleType(name);m.__file__=filename;sys.modules[name]=m
   exec(compile(base64.b64decode(P['controls'][filename]),filename,'exec'),m.__dict__)
  else:
   spec=importlib.util.spec_from_file_location(name,directory/filename)
   m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
  if name=='gcp_cfr_runner': engine=m
  else: cpu=m
def birth(pid):
 try:
  fields=pathlib.Path('/proc',str(pid),'stat').read_text().rsplit(')',1)[1].split()
  if fields[0]=='Z': return None
  return fields[19]
 except (FileNotFoundError,ProcessLookupError): return None
def handles(run,campaign,groups=None):
 groups=groups or {}
 found=[]
 for entry in pathlib.Path('/proc').iterdir():
  if not entry.name.isdigit() or int(entry.name)==os.getpid(): continue
  try:
   if entry.stat().st_uid!=986: continue
   args=(entry/'cmdline').read_bytes().decode(errors='replace').split('\0')
   role=None
   if len(args)>=4 and args[1:4]==['-',P['run'],'stage']: role='transport'
   elif len(args)>=3 and args[1]==str(run/'cpu_cfr_runner.py') and args[2]==str(run): role='runner'
   elif (entry/'comm').read_text().strip() in {'lean','lake'}:
    cwd=(entry/'cwd').resolve()
    if cwd==campaign or cwd.is_relative_to(campaign): role='compiler'
   stat=(entry/'stat').read_text().rsplit(')',1)[1].split()
   group=int(stat[2])
   if group in groups and (birth(group) is None or (groups[group] is not None and birth(group)==groups[group])): role='stage-process-group'
   token=birth(int(entry.name))
   if role and token: found.append(dict(pid=int(entry.name),start_ticks=token,role=role))
  except (FileNotFoundError,ProcessLookupError,PermissionError): pass
 return found
def write(path,value):
 with path.open('x',encoding='utf-8') as f: json.dump(value,f,indent=2)
def context():
 need(sys.platform=='linux' and os.getuid()==986,'Designated Linux worker required')
 need(cpu.observe()['host']==P['host'],'Wrong physical host')
 run=cpu.owned_path(P['remote_run'])
 need(run.name==P['run'],'Run path mismatch')
 return run
def preflight():
 run=context()
 guard=cpu.ResourceGuard(P['host'])
 record=cpu.owned_path(P['admission_path'])
 need(not record.is_relative_to(run),'Owner admission must preexist outside the staged run')
 raw=record.read_bytes();need(sha(raw)==P['admission_sha256'],'Owner admission record mismatch')
 admission=json.loads(raw);manifest=json.loads(base64.b64decode(P['manifest']))
 need(admission['status']=='ADMITTED' and admission['paper']=='P002','Owner has not admitted P002')
 need(admission['host']==P['host']==manifest['instance'],'Admission host mismatch')
 need(admission['run']==manifest['run']==P['run'],'Admission run mismatch')
 need(cpu.owned_path(admission['run_directory'])==run,'Owner run-directory mismatch')
 need(admission['capture_manifest_sha256']==P['manifest_sha256']==sha(base64.b64decode(P['manifest'])),'Manifest binding mismatch')
 need(admission['archive_sha256']==manifest['archive_sha256'],'Source archive binding mismatch')
 need(manifest['compile_host']=='CPU' and all(manifest.get(k) is None for k in ('project','zone','builder_profile')),'False cloud provenance')
 need(manifest['utf8_no_bom_verified'] and manifest['lean_toolchain']=='leanprover/lean4:v4.30.0','Encoding/toolchain mismatch')
 need(manifest['audit'] and manifest['targets'] and manifest['audited_exports'],'Explicit target/type/axiom audit required')
 need(admission['compiler_custody_reference'],'Missing compiler custody')
 controls={'cpu_cfr_runner.py':admission['runner_sha256'],'gcp_cfr_runner.py':admission['engine_sha256'],'cpu_cfr.py':admission['transport_sha256']}
 need(controls==manifest['execution_control_sha256'],'Execution-control binding mismatch')
 need(all(sha(base64.b64decode(P['controls'][n]))==h for n,h in controls.items()),'Transferred control changed')
 campaign=cpu.owned_path(admission['campaign'])
 need(not campaign.is_relative_to(run) and not run.is_relative_to(campaign),'Campaign/run overlap')
 need(cpu.owned_by_worker(campaign) and cpu.owned_by_worker(run.parent),'Worker-owned prepared campaign/run parent required')
 need((campaign/'packages').is_dir() and (campaign/'mathlib-cache').is_dir(),'Qualified dependencies/cache absent')
 provenance=cpu.owned_path(admission['dependency_provenance_path'])
 need(sha(provenance.read_bytes())==admission['dependency_provenance_sha256'],'Dependency provenance changed')
 origins=json.loads(provenance.read_text())
 need(origins['origin']=='fresh-public-pinned' and origins['packages']=={p['name']:p['rev'] for p in manifest['dependencies']},'Dependency origin/pins mismatch')
 tool=cpu.owned_path(admission['toolchain_bin'])
 need(set(admission['toolchain_sha256'])=={'lean','lake'},'Executable pins missing')
 need(all(engine.digest(tool/n)==h for n,h in admission['toolchain_sha256'].items()),'Executable changed')
 guard.check()
 return run,campaign,record,admission,manifest,guard,cpu.owned_path(admission['lease_file'])
def observation():
 run=context()
 if not run.exists():
  return dict(status='RUN_ABSENT',handles=handles(run,cpu.owned_path(P['campaign'])))
 claim=json.loads((run/'launch-request.json').read_text())
 need(claim['claim']==P['claim'] and claim['manifest_sha256']==P['manifest_sha256'] and claim['admission_sha256']==P['admission_sha256'],'Run custody mismatch')
 campaign=cpu.owned_path(claim['campaign'])
 terminal=json.loads((run/'terminal-receipt.json').read_text()) if (run/'terminal-receipt.json').exists() else None
 active=handles(run,campaign,{s['pid']:s.get('process_start_ticks') for s in (terminal or {}).get('stage_outcomes',[]) if s.get('pid',0)>0})
 completion=json.loads((run/'completion.json').read_text()) if (run/'completion.json').exists() else None
 status='ACTIVE' if active else 'TERMINAL' if completion or (terminal and terminal.get('status') in ('passed','failed')) else 'STOPPED_WITHOUT_TERMINAL'
 return dict(status=status,handles=active,terminal=terminal,completion=completion)
def perform():
 load_controls()
 if P['operation']=='screen':
  need(sys.platform=='linux' and os.getuid()==986,'Designated Linux worker required')
  value=cpu.observe()
  try: cpu.validate_observation(value,P['host']);status='RESOURCE_SCREEN_PASS_NOT_ADMISSION';reason=None
  except Exception as exc: status='REJECTED';reason=str(exc)
  return dict(status=status,reason=reason,observation=value,compiler_processes=cpu.compiler_processes())
 if P['operation']=='preflight':
  run,campaign,record,admission,manifest,guard,lease=preflight()
  with cpu.compiler_lease(lease):
   guard.check();need(not cpu.compiler_processes(),'Another compiler workload is active')
  need(not run.exists(),'Run already exists: observe instead of resubmitting')
  return dict(status='PREFLIGHT_PASS_NOT_LAUNCHED',host=P['host'])
 if P['operation']=='stage':
  run,campaign,record,admission,manifest,guard,lease=preflight()
  expected={'capture-manifest.json':P['manifest_sha256'],'inputs.tar.gz':manifest['archive_sha256'],'capture-controller.py':manifest['capture_controller_sha256'],**manifest['execution_control_sha256']}
  need(set(P['files'])==set(expected),'Unexpected upload file set')
  data={n:base64.b64decode(b) for n,b in P['files'].items()}
  need(sum(map(len,data.values()))<=64*2**20,'Upload exceeds bounded transport size')
  need(all(sha(data[n])==h for n,h in expected.items()),'Upload checksum mismatch')
  with cpu.compiler_lease(lease):
   guard.check();need(not cpu.compiler_processes(),'Another compiler workload is active')
   run.mkdir(mode=0o700) # Atomic, never overwrite an existing attempt.
   write(run/'launch-request.json',dict(claim=P['claim'],manifest_sha256=P['manifest_sha256'],admission_sha256=P['admission_sha256'],campaign=str(campaign),requested_utc=stamp(),transport_pid=os.getpid(),transport_start_ticks=birth(os.getpid())))
   for name,raw in data.items():
    with (run/name).open('xb') as f: f.write(raw)
   load_controls(run);os.environ['CFR_CPU_RUN']=P['run']
   cpu.validate_packet(run,campaign,admission,manifest);guard.check()
  # The child rechecks admission and acquires the host lease itself. A race
  # with a different lane fails closed; it never starts a concurrent compiler.
  with (run/'runner.stdout.txt').open('xb') as stdout,(run/'runner.stderr.txt').open('xb') as stderr:
   child=subprocess.Popen([sys.executable,str(run/'cpu_cfr_runner.py'),str(run),str(campaign),str(record),P['admission_sha256']],cwd=run,env={**os.environ,'CFR_CPU_RUN':P['run']},stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,start_new_session=True)
   write(run/'processes.json',dict(runner_pid=child.pid,runner_start_ticks=birth(child.pid),started_utc=stamp()))
   code=child.wait(timeout=cpu.MAX_SECONDS+90)
  write(run/'completion.json',dict(exit_code=code,finished_utc=stamp(),runner_pid=child.pid))
  return observation()
 if P['operation'] in ('observe','collect'):
  result=observation()
  if P['operation']=='observe': return result
  need(result['status'] not in ('ACTIVE','RUN_ABSENT'),'Collection requires stopped handles')
  run=cpu.owned_path(P['remote_run'])
  names=['launch-request.json','processes.json','completion.json','terminal-receipt.json','runner.stdout.txt','runner.stderr.txt','current-stage']
  terminal=result.get('terminal') or {}
  for name in terminal.get('log_sha256',{}):
   need(__import__('re').fullmatch(r'logs/(?:lean-version|lake-version|dependency-cache|dependency-cache-incremental|build|audit)\.(?:stdout|stderr)\.txt',name),'Unexpected log path')
   names.append(name)
  if terminal.get('type_axiom_audit',{}).get('emitted_types_sha256'): names.append('logs/emitted-types.json')
  files={}
  for name in names:
   path=run/name
   if path.exists():
    need(not path.is_symlink() and path.resolve().is_relative_to(run),'Unsafe collected path')
    raw=path.read_bytes();files[name]=dict(sha256=sha(raw),content=base64.b64encode(raw).decode())
  need(sum(len(base64.b64decode(v['content'])) for v in files.values())<=64*2**20,'Collection exceeds bounded transport size')
  result['files']=files
  return result
 raise RuntimeError('Unknown transport operation')
try: print(json.dumps(dict(ok=True,result=perform())),flush=True)
except Exception as exc: print(json.dumps(dict(ok=False,error=str(exc))),flush=True)
'''


def rpc(host, run, payload, timeout=45):
    require(host in ALIASES and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', run), 'Invalid transport identity')
    operation = payload['operation']
    require(operation in {'screen','preflight','stage','observe','collect'}, 'Invalid transport operation')
    ssh = 'C:/Windows/System32/OpenSSH/ssh.exe' if sys.platform == 'win32' else 'ssh'
    script = REMOTE_AGENT.replace('P = PAYLOAD', 'P = json.loads('+repr(json.dumps(payload))+')', 1)
    command = [ssh,'-o','BatchMode=yes','-o','StrictHostKeyChecking=yes','-o','IdentitiesOnly=yes',
               '-o','ConnectTimeout=10','-l','quantyra-worker',ALIASES[host],'python3 - '+run+' '+operation]
    result = subprocess.run(command,input=script,capture_output=True,text=True,timeout=timeout)
    require(result.returncode == 0, 'SSH transport failed: '+result.stderr[:500])
    answer = json.loads(result.stdout)
    require(answer.get('ok'), 'Remote operation rejected: '+str(answer.get('error')))
    return answer['result']


def packet(run_id):
    require(re.fullmatch(r'cfr-[A-Za-z0-9_.-]+',run_id), 'Invalid CPU capture run ID')
    path = ROOT/'evidence/cpu'/run_id
    raw = (path/'capture-manifest.json').read_bytes()
    manifest = json.loads(raw)
    require(manifest['run'] == run_id and manifest['compile_host'] == 'CPU' and manifest['instance'] in ALIASES, 'Invalid CPU packet identity')
    expected = {'capture-manifest.json':digest(raw),'inputs.tar.gz':manifest['archive_sha256'],
                'capture-controller.py':manifest['capture_controller_sha256'], **manifest['execution_control_sha256']}
    require(set(manifest['execution_control_sha256']) == set(CONTROL_NAMES), 'Recapture with exact transport/runner controls')
    files = {name:(path/name).read_bytes() for name in expected}
    require(sum(map(len,files.values())) <= MAX_BYTES, 'Packet exceeds bounded transport size')
    require(all(digest(files[name]) == sha for name,sha in expected.items()), 'Captured file/control changed')
    require(digest(Path(__file__).read_bytes()) == expected['cpu_cfr.py'], 'Use the exact captured transport controller')
    payload = dict(run=run_id, host=manifest['instance'], manifest=base64.b64encode(raw).decode(),
                   manifest_sha256=digest(raw), controls={name:base64.b64encode(files[name]).decode() for name in CONTROL_NAMES})
    return path, manifest, files, payload


def submit(run_id, admission_path, expected, call=rpc):
    path, manifest, files, payload = packet(run_id)
    admission_raw = Path(admission_path).read_bytes()
    require(digest(admission_raw) == expected, 'Local owner admission digest mismatch')
    admission = json.loads(admission_raw)
    require(admission['status'] == 'ADMITTED' and admission['paper'] == 'P002', 'P002 owner admission required')
    require(admission['run'] == run_id and admission['host'] == payload['host'], 'Owner admission identity mismatch')
    require(admission['capture_manifest_sha256'] == payload['manifest_sha256'], 'Owner manifest binding mismatch')
    require(admission['transport_sha256'] == manifest['execution_control_sha256']['cpu_cfr.py'], 'Owner transport binding mismatch')
    remote_run = WORKER_ROOT+'/runs/'+run_id
    require(admission['run_directory'] == remote_run, 'Owner must bind canonical run directory')
    payload.update(remote_run=remote_run, campaign=admission['campaign'], admission_path=admission['admission_path'], admission_sha256=expected)
    require(not (path/'submission-attempt.json').exists(), 'Submission already attempted: observe/collect; never restart automatically')
    preserved = path/'owner-admission.json'
    if preserved.exists():
        require(preserved.read_bytes() == admission_raw, 'Recorded owner admission changed')
    else:
        with preserved.open('xb') as output:
            output.write(admission_raw)
    checked = call(payload['host'],run_id,dict(payload,operation='preflight'))
    require(checked['status'] == 'PREFLIGHT_PASS_NOT_LAUNCHED', 'Preflight did not pass')
    claim = uuid.uuid4().hex
    journal = {key:payload[key] for key in ('host','remote_run','campaign','admission_path','admission_sha256','manifest_sha256')}
    journal.update(claim=claim,attempted_utc=now())
    write_new(path/'submission-attempt.json',journal) # Survives observation/SSH loss.
    response = call(payload['host'],run_id,dict(payload,operation='stage',claim=claim,
                    files={name:base64.b64encode(raw).decode() for name,raw in files.items()}),timeout=4*3600+180)
    write_new(path/'submission-response.json',response)
    return response


def observe_or_collect(run_id, collect=False, call=rpc):
    path, manifest, files, payload = packet(run_id)
    journal = json.loads((path/'submission-attempt.json').read_text())
    payload.update(journal,operation='collect' if collect else 'observe')
    response = call(payload['host'],run_id,payload)
    if not collect:
        return response
    require(response['status'] not in {'ACTIVE','RUN_ABSENT'}, 'No closed run evidence to collect')
    require(not response.get('handles'), 'A writer is still active')
    received = response.pop('files')
    data = {name:base64.b64decode(value['content']) for name,value in received.items()}
    for name, raw in data.items():
        require(evidence_name(name), 'Unsafe or unrequested collection name')
        require(digest(raw) == received[name]['sha256'], 'Collected file changed')
    terminal = response.get('terminal')
    if terminal:
        require('terminal-receipt.json' in data and json.loads(data['terminal-receipt.json']) == terminal,
                'Terminal metadata differs from collected bytes')
        require(terminal['run'] == run_id and terminal['compile_host'] == 'CPU', 'Terminal identity mismatch')
        require(terminal['source_sha256'] == manifest['source_sha256'] and terminal['dependencies'] == manifest['dependencies'], 'Terminal source/dependency mismatch')
        require(terminal['admission_sha256'] == journal['admission_sha256'], 'Terminal admission mismatch')
        require(terminal['runner_sha256'] == manifest['execution_control_sha256']['cpu_cfr_runner.py'] and
                terminal['engine_sha256'] == manifest['execution_control_sha256']['gcp_cfr_runner.py'] and
                terminal['transport_sha256'] == manifest['execution_control_sha256']['cpu_cfr.py'], 'Terminal control mismatch')
        require(terminal['instance'] == manifest['instance'] and terminal['worker_uid'] == 986, 'Terminal host/worker mismatch')
        require(terminal.get('status') in {'passed','failed'}, 'Nonterminal runner receipt')
        for name, sha in terminal.get('log_sha256',{}).items():
            require(name in data and digest(data[name]) == sha, 'Closed stage log missing/changed')
        if terminal['status'] == 'passed':
            owner_raw = (path/'owner-admission.json').read_bytes()
            require(digest(owner_raw) == journal['admission_sha256'], 'Preserved owner admission changed')
            owner = json.loads(owner_raw)
            require(terminal.get('source_and_dependencies_verified_before') and terminal.get('source_and_dependencies_verified_after'),
                    'Missing pre/post source/dependency verification')
            require(terminal.get('toolchain_binary_sha256') == owner['toolchain_sha256'] and
                    terminal.get('lean_commit_verified') == 'd024af099ca4bf2c86f649261ebf59565dc8c622', 'Compiler identity mismatch')
            stages = terminal.get('stage_outcomes',[])
            require(all(s['exit_code'] == 0 and not s['timed_out'] for s in stages), 'Failed stage in passing receipt')
            require(all('logs/'+s['stage']+'.'+stream+'.txt' in terminal['log_sha256']
                        for s in stages for stream in ('stdout','stderr')), 'Stage output omitted from closed-log inventory')
            build = [s for s in stages if s['stage'] == 'build']
            audit = [s for s in stages if s['stage'] == 'audit']
            require(len(build) == len(audit) == 1 and build[0]['command'] == ['lake','build',*manifest['targets']], 'Missing/mismatched build or audit')
            require(audit[0]['command'] == ['lake','env','lean',manifest['audit_path']], 'Audit command differs')
            require(set(terminal.get('audited_declarations',[])) == set(manifest['audited_exports']) and
                    set(terminal.get('reported_axioms',[])) <= {'propext','Classical.choice','Quot.sound'}, 'Audit coverage/axioms differ')
            audit_binding = terminal.get('type_axiom_audit',{})
            require('logs/emitted-types.json' in data and digest(data['logs/emitted-types.json']) == audit_binding.get('emitted_types_sha256'),
                    'Missing or changed emitted declaration types')
            types=json.loads(data['logs/emitted-types.json'])
            require(set(types) == set(manifest['audited_exports']), 'Emitted declaration coverage differs')
            for name,value in types.items():
                actual=digest(value['emitted_type'].encode('utf-8'))
                require(value['emitted_type'].strip() and actual == value['sha256'] == audit_binding['type_block_sha256'][name],
                        'Emitted declaration type fingerprint differs')
    out = path/('collected-'+uuid.uuid4().hex)
    out.mkdir()
    for name, raw in data.items():
        target=out/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
    receipt = dict(observed_utc=now(),run=run_id,remote_state=response,
                   files={n:digest(b) for n,b in data.items()},semantic_acceptance=False)
    write_new(out/'collection.json',receipt)
    return dict(collection=str(out),remote_status=response['status'],semantic_acceptance=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='mode',required=True)
    screen=sub.add_parser('screen');screen.add_argument('--host',choices=sorted(ALIASES),required=True)
    for name in ['submit','observe','collect']:
        command=sub.add_parser(name);command.add_argument('--run',required=True)
        if name=='submit':
            command.add_argument('--admission',required=True);command.add_argument('--admission-sha256',required=True)
    args=parser.parse_args()
    if args.mode=='screen':
        controls={name:base64.b64encode((ROOT/'tools'/name).read_bytes()).decode() for name in CONTROL_NAMES}
        result=rpc(args.host,'cpu-screen',dict(operation='screen',host=args.host,controls=controls))
    elif args.mode=='submit': result=submit(args.run,args.admission,args.admission_sha256)
    else: result=observe_or_collect(args.run,collect=args.mode=='collect')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
