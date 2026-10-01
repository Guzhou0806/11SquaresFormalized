"""Bounded low-priority dispatcher with case-priority scheduling and shared-proof backfill.

Adopts already running checks without interrupting them. One scheduling loop
reserves exact unverified source closures across both kinds of work, allowing
future collision cases to be published safely. Proof validity remains entirely
with the original checker and its genuine hash receipts.
"""
from pathlib import Path
import json,subprocess,sys,time,datetime,os,argparse,zipfile,hashlib
ap=argparse.ArgumentParser()
from retry_paths import kit_paths,low_priority_single_core,metadata_path
ap.add_argument('--kit',required=True);ap.add_argument('--runtime-root',required=True)
ap.add_argument('--transport-dir');ap.add_argument('--scratch-root',required=True)
ap.add_argument('--max-workers',type=int,choices=[4,6],default=4)
ap.add_argument('--probe-script',type=Path,required=True)
ap.add_argument('--poll-seconds',type=int,default=5)
args=ap.parse_args();assert 1<=args.poll_seconds<=60
K,E,transport_root=kit_paths(args.kit,args.transport_dir)
B=Path(args.runtime_root).resolve();scratch=Path(args.scratch_root).resolve()
assert B.is_dir() and scratch.is_dir() and args.probe_script.is_file()
assert sys.platform=='linux','Controller process ownership requires Linux'
import fcntl
low_priority_single_core()
from pool_helpers import build_helpers
h=build_helpers(K,B,transport_root)
info=h['archive_info'];valid=h['valid'];logdone=h['logdone'];completed=h['completed_cases']
guard=(B/'unified-proof-pool-v7.lock').open('w');fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
maximum_workers=args.max_workers
assert maximum_workers in [4,6]
case_workers=['primary','independent-probe','helper-probe']+(['extra-a'] if maximum_workers==6 else [])
library_workers=['library-b']+(['library-c'] if maximum_workers==6 else [])
prefix={'primary':'primary','independent-probe':'independent','helper-probe':'helper','extra-a':'extra-a'};prefix.update({w:w for w in library_workers})
inventory=h['inventory'];events=[];active={};attempted=set()
def event(**r):
 r['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();events.append(r);print(json.dumps(r),flush=True)
 payload=dict(active={w:{k:v for k,v in j.items() if k in ['task','case','kind','pid']} for w,j in active.items()},events=events)
 temp=E/'unified-proof-pool-status.writing.json';temp.write_text(json.dumps(payload,indent=2)+'\n');temp.replace(E/'unified-proof-pool-status.json')
def pending(archive):return {n for n,k in info(archive).items() if not valid(n,k)}
def alive(j):
 if 'process' in j:return j['process'].poll() is None
 try:args=Path(f"/proc/{j['pid']}/cmdline").read_bytes().split(b'\0')
 except OSError:return False
 return j['task'].encode() in args and str(globals()['args'].probe_script).encode() in args
adoption=json.loads((E/'unified-pool-adoption-v7.json').read_text())
events.extend(adoption.get('prior_events',[]))
attempted.update(adoption['attempted_tasks'])
case_schedule={}
for previous_event in events:
 if previous_event.get('status')=='CHECK_STARTED' and previous_event.get('kind')=='library':
  name=previous_event['task']
  if name.startswith('library-case'):
   number=int(name.split('library-case',1)[1].split('-',1)[0])
   case_schedule[number]=datetime.datetime.fromisoformat(previous_event['utc']).timestamp()
for row in adoption['jobs']:
 archive=transport_root/row['archive']
 # An owned controller restart may reserve every source member of an active
 # immutable transport. This safely over-reserves its closure and avoids
 # rehashing large active jobs before any new work can be dispatched. These
 # reservations never create receipts or bypass the supplied proof checker.
 reserved_members=row.get('conservative_reserved_modules')
 active[row['worker']]=dict(row,reserved=set(reserved_members) if reserved_members is not None else pending(archive))
 attempted.add(row['task'])
event(status='RESUMED_WITH_BOUNDED_RESOURCES',workers=case_workers+library_workers,maximum_parallel_checks=maximum_workers,lean_threads=1,completed_at_resume=len(completed()),controller_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
while True:
 for worker,j in list(active.items()):
  if alive(j):continue
  if 'handle' in j:j['handle'].close()
  log=E/(prefix[worker]+'-'+Path(j['task']).stem+'.log')
  receipt=E/(prefix[worker]+'-'+Path(j['task']).stem+'.json')
  try:passed=logdone(log) and json.loads(receipt.read_text())['exit_code']==0
  except (OSError,ValueError,KeyError):passed=False
  del active[worker]
  event(status='CHECK_PASSED' if passed else 'CHECK_FAILED',worker=worker,task=j['task'],kind=j['kind'],case=j.get('case'))
  subprocess.run([sys.executable,str(E/'record_resumed_progress.py')],stdout=subprocess.DEVNULL)
 # The pre-existing helper queue retains its runtime until its final case exits.
 available=[w for w in case_workers if w not in active and (w.startswith('extra-') or h['gate_open'](w))]
 free_libraries=[w for w in library_workers if w not in active]
 mem_available=int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))
 if len(completed())<173 and mem_available>4*1024*1024 and (available or free_libraries):
  reserved=h['externally_reserved']()
  for j in active.values():reserved.update(j['reserved'])
  candidates=[];done=completed()
  for task in E.glob('forward-case*-assembly-task.json'):
   case=int(task.name.split('forward-case')[1].split('-')[0])
   if (E/f'.collision-bool-preparing-case{case}.json').exists():continue
   if case in done or task.name in attempted:continue
   archive=transport_root/('.t03-runtime-sync-'+task.stem+'.zip')
   if archive.exists():
    metadata=json.loads(task.read_text())
    grouped=any('.PackedNamespaced' in m for m in metadata['modules'])
    candidates.append(dict(task=task.name,archive=archive,case=case,kind='case',grouped=grouped))
  candidates.sort(key=lambda r:('retry' not in r['task'] and not r['grouped'],inventory[r['case']]['inputs']+inventory[r['case']]['partner_inputs']))
  for queue in sorted(E.glob('library-case*-node*-queue.json')):
   library_case=int(queue.name.split('library-case')[1].split('-')[0])
   if library_case in done:continue
   try:rows=json.loads(queue.read_text())['tasks']
   except (OSError,ValueError):continue
   for row in rows:
    task=row['task']
    if task in attempted:continue
    archive=transport_root/('.t03-runtime-sync-'+Path(task).stem+'.zip')
    # Unissued batches have no source transport and cannot be scheduled.
    # Avoid probing every worker's historical logs for those thousands of rows.
    if not archive.exists():continue
    if any(logdone(E/(p+'-'+Path(task).stem+'.log')) for p in ['primary','independent','helper','auxiliary','extra-a','extra-b','extra-c','extra-d','extra-e','extra-f','library-a','library-b','library-c','library-d','library-e','library-f']):continue
    candidates.append(dict(task=task,archive=archive,kind='library',dependency_path=row.get('remaining_dependency_path_groups',0),
        bounded_timing_probe=task=='library-case1465-node997-audit-timing-probe-task.json' and row.get('bounded_timing_probe',False)))
  # Give ready cases with fewer active checks a slot first, rotate the oldest
  # waiting case next, and choose its longest dependency path. Update counts
  # after each assignment so simultaneous free slots rotate between cases.
  group_counts={}
  for job in active.values():
   if job['kind']=='library':
    number=int(job['task'].split('library-case',1)[1].split('-',1)[0])
    group_counts[number]=group_counts.get(number,0)+1
  def candidate_priority(row):
   if row['kind']=='case':return (0,0,0,0)
   if row.get('bounded_timing_probe'):return (1,-1,0,0)
   number=int(row['task'].split('library-case',1)[1].split('-',1)[0])
   return (1,group_counts.get(number,0),case_schedule.get(number,0),-row.get('dependency_path',0))
  while candidates:
   candidate=min(candidates,key=candidate_priority);candidates.remove(candidate)
   if candidate['task'] in attempted:continue
   if candidate['kind']=='case' and (E/f".collision-bool-preparing-case{candidate['case']}.json").exists():continue
   slots=available if candidate['kind']=='case' else (free_libraries if free_libraries else available)
   if not slots:continue
   try:needed=pending(candidate['archive'])
   except (OSError,ValueError,KeyError,zipfile.BadZipFile):continue
   if needed&reserved:continue
   if candidate['kind']=='case' and (E/f".collision-bool-preparing-case{candidate['case']}.json").exists():continue
   worker=slots.pop(0);handle=(E/(worker+'-unified-dispatcher.log')).open('a')
   process=subprocess.Popen([sys.executable,str(args.probe_script),candidate['archive'].name,candidate['task'],'--worker',worker,'--kit',str(K),'--runtime-root',str(B),'--transport-dir',str(transport_root),'--scratch-root',str(scratch),'--max-workers',str(maximum_workers)],stdout=handle,stderr=subprocess.STDOUT)
   job=dict(candidate,pid=process.pid,process=process,handle=handle,reserved=needed)
   active[worker]=job;attempted.add(candidate['task']);reserved.update(needed)
   event(status='CHECK_STARTED',worker=worker,task=candidate['task'],kind=candidate['kind'],case=candidate.get('case'),unverified_modules=len(needed))
   if candidate['kind']=='library' and not candidate.get('bounded_timing_probe'):
    number=int(candidate['task'].split('library-case',1)[1].split('-',1)[0])
    group_counts[number]=group_counts.get(number,0)+1
    case_schedule[number]=datetime.datetime.fromisoformat(events[-1]['utc']).timestamp()
   if not available and not free_libraries:break
 if len(completed())==173 and not active:
  event(status='ALL_173_CASE_CERTIFICATES_PASSED');break
 time.sleep(args.poll_seconds)
