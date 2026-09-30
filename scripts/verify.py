#!/usr/bin/env python3
"""Serial Lean replay and axiom audit of the partially formalized repository."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
sys.dont_write_bytecode = True
import time
from check_sources import ROOT, check, imports

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--setup', action='store_true', help='Install the pinned public toolchain and dependency cache.')
ap.add_argument('--all', action='store_true', help='Check every included local source module.')
ap.add_argument('--fresh', action='store_true', help='Ignore this checkout\'s matching accepted receipts.')
ap.add_argument('--plan', action='store_true', help='Print dependency order without installing or compiling.')
args = ap.parse_args()
print(json.dumps(check()), flush=True)
files = sorted((ROOT / 'ElevenSquare').rglob('*.lean')) + [ROOT / 'ElevenSquare.lean']
modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in files}
order = []; done = set()
def visit(m):
    if m in done or m not in modules: return
    for dep in imports(modules[m]): visit(dep)
    done.add(m); order.append(m)
if args.all:
    for m in sorted(modules):
        if m != 'ElevenSquare.Verification': visit(m)
visit('ElevenSquare.Verification')
# Even --all ends at the target audit, which must use the completed dependencies.
order.remove('ElevenSquare.Verification'); order.append('ElevenSquare.Verification')
if args.plan:
    print('Serial local module checks:', len(order))
    print('\n'.join(order))
    raise SystemExit(0)

state = ROOT / '.verification'
state.mkdir(exist_ok=True)
child = None
signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
def run(command, **kwargs):
    global child
    child = subprocess.Popen(command, cwd=ROOT, **kwargs)
    try:
        code = child.wait()
    except BaseException:
        child.terminate()
        try: child.wait(timeout=3)
        except subprocess.TimeoutExpired:
            child.kill(); child.wait()
        raise
    finally:
        child = None
    if code: raise SystemExit(code)

bin_dir = Path.home() / '.elan/bin'
env = os.environ.copy()
if bin_dir.is_dir(): env['PATH'] = str(bin_dir) + os.pathsep + env.get('PATH', '')
elan = shutil.which('elan', path=env['PATH'])
lake = shutil.which('lake', path=env['PATH'])
if not elan or not lake:
    raise SystemExit('Install elan and make its bin directory available, then retry.')
if args.setup:
    run([elan, 'toolchain', 'install', (ROOT / 'lean-toolchain').read_text().strip()], env=env)
    run([lake, 'exe', 'cache', 'get'], env=env)
# Read only the scoped Lean executable/path, not the full user environment.
runtime = json.loads(subprocess.check_output(
    [lake, 'env', sys.executable, '-c',
     "import os,shutil,json; print(json.dumps({'lean':shutil.which('lean'), 'path':os.environ.get('LEAN_PATH','')}))"],
    cwd=ROOT, env=env, text=True))
lean_env = env.copy(); lean_env['LEAN_PATH'] = runtime['path']
version = subprocess.check_output([runtime['lean'], '--version'], cwd=ROOT, env=lean_env, text=True).strip()
if '4.10.0-rc2' not in version:
    raise SystemExit('Unexpected Lean version; use the pinned lean-toolchain.')

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(4 << 20), b''): h.update(b)
    return h.hexdigest()

def object_path(m): return ROOT / '.lake/build/lib' / (m.replace('.', '/') + '.olean')

accepted = 0
for index, m in enumerate(order):
    src = modules[m]; rel = str(src.relative_to(ROOT)); target = object_path(m)
    target.parent.mkdir(parents=True, exist_ok=True)
    receipt = state / (m + '.json'); log = state / (m + '.log')
    deps = {d: sha(object_path(d)) for d in imports(src) if d in modules}
    fingerprint = {'source': sha(src), 'local_dependency_objects': deps, 'compiler': version,
                   'arguments': ['-j1', '-M0', '-s65536', '-DautoImplicit=false', '-DmaxHeartbeats=0']}
    old = json.loads(receipt.read_text()) if receipt.is_file() else {}
    if (not args.fresh and target.is_file() and old.get('status') == 'accepted'
            and old.get('inputs') == fingerprint and old.get('object_sha256') == sha(target)
            and log.is_file()):
        print(f'[{index+1}/{len(order)}] cached {m}', flush=True)
        accepted += 1; continue
    tmp = target.with_name(target.name + '.checking')
    started = time.monotonic()
    try:
        with log.open('w') as stream:
            run([runtime['lean'], '--root=.', '-j1', '-M0', '-s65536', '-DautoImplicit=false',
                 '-DmaxHeartbeats=0', '-o', str(tmp.relative_to(ROOT)), rel], env=lean_env,
                stdout=stream, stderr=subprocess.STDOUT)
        os.replace(tmp, target)
    except BaseException:
        if tmp.exists(): tmp.unlink()
        receipt.write_text(json.dumps({'module':m, 'status':'failed_or_interrupted', 'inputs':fingerprint}, indent=2)+'\n')
        print(log.read_text()[-4000:], file=sys.stderr)
        raise
    receipt.write_text(json.dumps({'module':m, 'status':'accepted', 'inputs':fingerprint,
                                  'object_sha256':sha(target), 'elapsed_seconds':round(time.monotonic()-started, 2)}, indent=2)+'\n')
    accepted += 1
    print(f'[{index+1}/{len(order)}] accepted {m}', flush=True)

import re
text = (state / 'ElevenSquare.Verification.log').read_text()
seen = {n:{a.strip() for a in ax.split(',') if a.strip()}
        for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)}
seen.update({n:set() for n in re.findall(r"'([^']+)' does not depend on any axioms", text)})
queries = re.findall(r'^#print axioms (\S+)', modules['ElevenSquare.Verification'].read_text(), re.M)
unfinished = {'ElevenSquare.Pending.'+n for n in ['baseline_certificate_exists','prior_certificate_exists',
              'returned_certificate_exists','global_lower_bound']} | {'ElevenSquare.optimality'}
allowed = {'propext','Classical.choice','Quot.sound'}
for n in queries:
    if n not in seen: raise SystemExit('Missing axiom output: '+n)
    extra = seen[n] - allowed - ({'sorryAx'} if n in unfinished else set())
    if extra: raise SystemExit('Unapproved axioms in '+n+': '+str(sorted(extra)))
result = {'status':'PARTIAL_ASSEMBLY_COMPILES', 'checked_modules':accepted,
          'axioms':{n:sorted(seen[n]) for n in queries},
          'global_optimality_proved':not any('sorryAx' in seen[n] for n in unfinished)}
(state / 'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
print('Partial assembly accepted. See MISSING.md for the remaining proof obligations.')
