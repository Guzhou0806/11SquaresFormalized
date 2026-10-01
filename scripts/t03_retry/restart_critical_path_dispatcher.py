"""Adopt live proof workers and apply global critical-path scheduling."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,signal,subprocess,sys,time,zipfile

ap=argparse.ArgumentParser();ap.add_argument('--revision',type=int,default=1)
from retry_paths import kit_paths,low_priority_single_core,metadata_path
ap.add_argument('--kit',required=True);ap.add_argument('--runtime-root',required=True)
ap.add_argument('--transport-dir');ap.add_argument('--scratch-root',required=True)
ap.add_argument('--controller-script',type=Path,required=True)
ap.add_argument('--probe-script',type=Path,required=True)
ap.add_argument('--owned-controller-pid',type=int,required=True)
ap.add_argument('--max-workers',type=int,choices=[4,6],default=4)
args=ap.parse_args();revision=args.revision;assert 1<=revision<=99
K,E,transport_root=kit_paths(args.kit,args.transport_dir);B=Path(args.runtime_root).resolve()
assert sys.platform=='linux','Process ownership requires Linux'
assert args.controller_script.is_file() and args.probe_script.is_file()
low_priority_single_core()
suffix='' if revision==1 else f'-retry{revision:02d}'
record=E/('critical-path-dispatcher-transition'+suffix+'.json');assert not record.exists()

def argv(pid):
 try:return Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
 except OSError:return []

def atomic_json(path,payload):
 temp=path.with_suffix('.writing.json')
 temp.write_text(json.dumps(payload,indent=2)+'\n');temp.replace(path)

old=args.owned_controller_pid;retired=False
assert str(args.controller_script).encode() in argv(old), 'Owned PID must run the exact supplied controller'
adoption_path=E/'unified-pool-adoption-v7.json'
backup=E/('unified-pool-adoption-v7-before-critical-path'+suffix+'.json')
assert adoption_path.exists() and not backup.exists()
os.kill(old,signal.SIGSTOP)
try:
 pool=json.loads((E/'unified-proof-pool-status.json').read_text())
 jobs={w:dict(j,worker=w,archive='.t03-runtime-sync-'+Path(j['task']).stem+'.zip')
       for w,j in pool['active'].items()}
 allowed={'primary','independent-probe','helper-probe','extra-a','library-b','library-c'}
 live={}
 for path in Path('/proc').glob('[0-9]*/cmdline'):
  pid=int(path.parent.name);process_args=argv(pid)
  if not str(globals()['args'].probe_script).encode() in process_args:continue
  index=next(i for i,a in enumerate(process_args) if a==str(globals()['args'].probe_script).encode())
  archive,task=(value.decode() for value in process_args[index+1:index+3])
  worker=process_args[process_args.index(b'--worker')+1].decode() if b'--worker' in process_args else process_args[index+3].decode()
  assert worker in allowed and worker not in live
  assert Path(archive).name==archive and archive=='.t03-runtime-sync-'+Path(task).stem+'.zip'
  kind='case' if task.startswith('forward-case') else 'library'
  assert kind=='case' or task.startswith('library-case')
  row=dict(pid=pid,task=task,worker=worker,archive=archive,kind=kind)
  if kind=='case':row['case']=int(task.split('forward-case',1)[1].split('-',1)[0])
  if worker in jobs and jobs[worker]['pid']!=pid:
   previous=jobs[worker]
   assert previous['task'].encode() not in argv(previous['pid'])
  live[worker]=row;jobs[worker]=row
 assert len(live)<=globals()['args'].max_workers
 for worker,row in jobs.items():
  if worker not in live:
   prefix={'independent-probe':'independent','helper-probe':'helper'}.get(worker,worker)
   execution=E/(prefix+'-'+Path(row['task']).stem+'.json')
   assert execution.exists(),('Missing receipt for finished adopted job',row)
   row['conservative_reserved_modules']=[]
   continue
  archive=transport_root/row['archive']
  before=archive.stat()
  with zipfile.ZipFile(archive) as z:
   manifest=json.loads(z.read('source-sync-manifest.json'))
   task_bytes=z.read(row['task'])
   assert hashlib.sha256(task_bytes).hexdigest()==manifest[row['task']]
   assert json.loads(task_bytes)==json.loads((E/row['task']).read_text())
   row['conservative_reserved_modules']=sorted(n[8:-5].replace('/','.') for n in manifest
       if n.startswith('project/ElevenSquare/') and n.endswith('.lean'))
   assert row['conservative_reserved_modules']
   row['reservation_manifest_sha256']=hashlib.sha256(z.read('source-sync-manifest.json')).hexdigest()
  after=archive.stat()
  assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns)
 attempted={r['task'] for r in pool['events'] if r.get('status')=='CHECK_STARTED'}|{r['task'] for r in jobs.values()}
 original_adoption=adoption_path.read_bytes();backup.write_bytes(original_adoption)
 assert backup.read_bytes()==original_adoption
 atomic_json(adoption_path,dict(jobs=list(jobs.values()),attempted_tasks=sorted(attempted),
   prior_events=pool['events'],reservation_method='Conservatively reserve all active transport source members; never substitute for actual proof or receipt validation.'))
 os.kill(old,signal.SIGTERM);os.kill(old,signal.SIGCONT)
 deadline=time.monotonic()+10
 while str(args.controller_script).encode() in argv(old):
  assert time.monotonic()<deadline;time.sleep(.1)
 retired=True
 log=(E/'unified-proof-pool-v7.log').open('a')
 process=subprocess.Popen([sys.executable,'-u',str(args.controller_script),'--kit',str(K),'--runtime-root',str(B),'--transport-dir',str(transport_root),'--scratch-root',args.scratch_root,'--probe-script',str(args.probe_script),'--max-workers',str(args.max_workers)],
   env=dict(os.environ,T03_MAX_WORKERS=str(args.max_workers)),stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 payload=dict(status='GLOBAL_CRITICAL_PATH_CONTROLLER_STARTED_EXISTING_PROOF_WORKERS_ADOPTED',
   utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),old_dispatcher=old,new_dispatcher=process.pid,
   active_workers=[{k:v for k,v in row.items() if k!='conservative_reserved_modules'} for row in jobs.values()],
   live_proof_worker_count=len(live),maximum_parallel_checks=args.max_workers,
   original_adoption_preserved=backup.name,original_adoption_sha256=hashlib.sha256(original_adoption).hexdigest(),
   changes=['Prefer fewer active group checks, then rotate the oldest waiting case, then choose its longest dependency path.',
            'Update case counts after each assignment so simultaneous free slots serve different waiting cases.',
            'Check whether a prepared source archive exists before probing historical proof logs.',
            'Poll every five seconds after reducing unissued-batch filesystem probes.',
            'Conservatively reserve active source closures without rehashing proof caches at adoption.',
            'Keep full-case priority and ordinary exact candidate receipt checks.'],
   controller_source_sha256=hashlib.sha256(args.controller_script.read_bytes()).hexdigest(),
   running_proof_workers_unchanged=True,compiler_processes_interrupted=0)
 atomic_json(record,payload);print(json.dumps(payload),flush=True)
finally:
 if not retired:
  try:os.kill(old,signal.SIGCONT)
  except ProcessLookupError:pass
