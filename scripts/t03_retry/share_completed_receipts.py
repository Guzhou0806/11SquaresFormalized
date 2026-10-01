"""Copy existing genuine receipts from both runtime locations; never prove a target.

A current compiled-object hash gates each copy. The original handoff checker
must still validate the full source closure and object hashes before reuse.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, time
DEFAULT_WORKERS=['primary','independent-probe','helper-probe','auxiliary-probe','extra-a','extra-b','extra-c','extra-d','extra-e','extra-f','library-a','library-b','library-c','library-d','library-e','library-f']

def reconcile(runtime_roots,workers,destination,object_root,seen,objects):
    copied=[]
    for worker in workers:
        for root in runtime_roots:
            for src in (root/worker/'project/verification/handoff-cache').glob('*.json'):
                try:
                    s=src.stat();signature=(s.st_size,s.st_mtime_ns)
                    if seen.get(src)==signature:continue
                    raw=src.read_bytes();r=json.loads(raw);dest=destination/src.name
                    if dest.exists() and dest.read_bytes()==raw:seen[src]=signature;continue
                    if not re.fullmatch(r'ElevenSquare(?:\.[A-Za-z0-9_]+)+',src.stem):continue
                    obj=object_root/Path(*src.stem.split('.')).with_suffix('.olean')
                    s=obj.stat();key=(s.st_size,s.st_mtime_ns)
                    if obj not in objects or objects[obj][0]!=key:
                        objects[obj]=(key,hashlib.sha256(obj.read_bytes()).hexdigest())
                    if objects[obj][1]!=r['object_sha256']:continue
                    temp=dest.with_suffix('.sharing-tmp');temp.write_bytes(raw);os.replace(temp,dest)
                    seen[src]=signature
                    copied.append({'module':src.stem,'worker':worker,'receipt_sha256':hashlib.sha256(raw).hexdigest()})
                except (OSError,ValueError,KeyError):continue
    return copied

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--runtime-root',type=Path,required=True)
    p.add_argument('--scratch-root',type=Path)
    p.add_argument('--destination',type=Path)
    p.add_argument('--object-root',type=Path)
    p.add_argument('--worker',action='append')
    p.add_argument('--interval-seconds',type=int,default=60)
    p.add_argument('--once',action='store_true')
    a=p.parse_args()
    if os.name!='posix':p.error('The daemon uses Linux file locking; --help is available everywhere.')
    if a.interval_seconds<1:p.error('Interval must be positive.')
    workers=a.worker or DEFAULT_WORKERS
    if any(not re.fullmatch(r'[A-Za-z0-9_-]+',w) for w in workers):p.error('Worker names must be directory names.')
    roots=[a.runtime_root]+([a.scratch_root] if a.scratch_root else [])
    destination=a.destination or a.runtime_root/'project/verification/handoff-cache'
    object_root=a.object_root or a.runtime_root/'lake/build/lib'
    destination.mkdir(parents=True,exist_ok=True)
    import fcntl
    os.nice(10)
    if hasattr(os,'sched_setaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
    lock=(a.runtime_root/'receipt-sharing.lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    seen={};objects={}
    while True:
        copied=reconcile(roots,workers,destination,object_root,seen,objects)
        if copied:print(json.dumps({'status':'EXISTING_RECEIPTS_SHARED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'count':len(copied),'sample':copied[:3]}),flush=True)
        if a.once:
            print(json.dumps({'status':'RECEIPT_RECONCILIATION_COMPLETE','checked_receipts':len(seen)}),flush=True);return
        time.sleep(a.interval_seconds)
if __name__=='__main__':main()
