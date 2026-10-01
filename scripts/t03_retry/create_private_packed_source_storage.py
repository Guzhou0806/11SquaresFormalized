"""Redirect only a fresh private packed-source directory to authorized D: scratch.

The final exact-source transport and exporter staging read logical module paths
and write fresh physical source files; no junction enters the final return ZIP.
"""
from pathlib import Path
import argparse, datetime, json, subprocess, sys

from retry_paths import kit_paths, low_priority_single_core
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--max-workers',type=int,default=1)
ap.add_argument('--source-root',type=Path)
ap.add_argument('--wsl-distro',default='Ubuntu')
a=ap.parse_args();case=a.case
assert sys.platform=='win32', 'Junction storage requires Windows'
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
scratch=Path(a.scratch_root).resolve();assert scratch.is_dir()
assert 1<=a.max_workers<=6
low_priority_single_core()
S=a.source_root.resolve() if a.source_root else K/'eleven-square-lean'
assert case in {r['case'] for r in json.loads((E / 'forward-workload-inventory.json').read_text())['records']}
task = json.loads((E / f'forward-case{case}-assembly-task.json').read_text())
assert len(task['modules']) == 1 and task['modules'][0].endswith(f'.Case{case}.Forward.Certificate')
module = task['modules'][0].removesuffix('.Forward.Certificate') + '.PackedNamespaced'
assert module.startswith('ElevenSquare.Tasks.T03.Batch')
logical = S / module.replace('.', '/')
assert logical.parent.resolve().is_relative_to((S / 'ElevenSquare/Tasks/T03').resolve())
assert not logical.exists() and not logical.is_symlink()
assert not (E / f'case{case}-packed-namespaced-publication.json').exists()
assert not any(j.get('case') == case for j in json.loads((E / 'unified-proof-pool-status.json').read_text())['active'].values())
assert case not in {r['case'] for r in json.loads((E / 'RESULT.json').read_text())['audited_case_certificates']}

physical = scratch / 'private-packed-sources' / f'case{case}' / 'PackedNamespaced'
assert physical.resolve().is_relative_to(scratch.resolve()) and not physical.exists()
record = E / f'case{case}-private-packed-source-storage.json'
assert not record.exists()
physical.mkdir(parents=True)
logical.parent.mkdir(parents=True, exist_ok=True)
def ps_quote(value):
    return "'" + str(value).replace("'", "''") + "'"
command = 'New-Item -ItemType Junction -Path ' + ps_quote(logical) + ' -Target ' + ps_quote(physical) + ' -ErrorAction Stop | Out-Null'
subprocess.run(['powershell.exe', '-NoProfile', '-Command', command], check=True)
assert logical.resolve() == physical.resolve()
probe = logical / '.storage-probe.txt'
probe.write_bytes(b'T03 exact private packed source storage\n')
assert (physical / probe.name).read_bytes() == probe.read_bytes()
import re
value=str(probe.absolute()).replace(chr(92),'/')
match=re.fullmatch(r'([A-Za-z]):/(.*)',value)
assert match, 'Supply a drive-based logical source path'
posix='/mnt/'+match[1].lower()+'/'+match[2]
subprocess.run(['wsl.exe', '-d', a.wsl_distro, '--', 'python3', '-c',
                'import pathlib,sys; assert pathlib.Path(sys.argv[1]).read_bytes()==b"T03 exact private packed source storage\\n"', posix], check=True)
assert probe.resolve().parent == physical.resolve()
probe.unlink()
p = dict(status='FRESH_PRIVATE_PACKED_SOURCE_STORAGE_WINDOWS_AND_WSL_VERIFIED',
         case=case, utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         logical_owned_module_directory=str(logical), physical_directory=str(physical),
         original_source_files_unchanged=True, active_source_closures_unchanged=True,
         lean_processes_started=0, proof_checks_pending=True,
         final_exporter_uses_fresh_physical_source_staging=True)
record.write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps(p), flush=True)
