"""Compare exact source synchronization on disposable fixtures; start no Lean."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time, zipfile
import argparse
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--archive',type=Path,required=True)
ap.add_argument('--expected-sha256',required=True)
ap.add_argument('--scratch-root',type=Path,required=True)
ap.add_argument('--native-python',required=True)
ap.add_argument('--helper',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args()
assert sys.platform == 'linux', 'Run this comparison from WSL'
os.nice(10)
os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
native=a.native_python
archive=a.archive.resolve()
expected=a.expected_sha256
def win(path):
    import re
    value=str(path.resolve())
    match=re.fullmatch(r'/mnt/([a-zA-Z])/(.*)',value)
    assert match, 'Supply a drive-mounted path accessible to native Python'
    return match[1].upper()+':/'+match[2]
helper=win(a.helper)
root=a.scratch_root.resolve()/'grouped-source-runtimes'
native_runtime=root/'validation-source-sync'
linux_runtime=root/'validation-source-sync-linux'
assert not native_runtime.exists() and not linux_runtime.exists()
record=a.output
assert not record.exists()
h=hashlib.sha256()
with archive.open('rb') as f:
    for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
assert h.hexdigest()==expected
def native_run(digest=expected):
    command = [native, helper, '--scratch-root', win(a.scratch_root), '--archive', win(archive), '--runtime', win(native_runtime),
               '--expected-sha256', digest, '--skip-receipts']
    p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if p.returncode:
        return p.returncode, p.stdout
    return 0, json.loads(p.stdout.strip())
code, first = native_run()
assert code == 0 and first['proof_receipts_created'] == first['lean_processes_started'] == 0
print(json.dumps(dict(stage='NATIVE_FIRST_SYNC_MEASURED', seconds=first['total_seconds'], members=first['verified_members'])), flush=True)
started = time.monotonic()
with zipfile.ZipFile(archive) as z:
    manifest = json.loads(z.read('source-sync-manifest.json'))
    for name, digest in manifest.items():
        raw = z.read(name)
        assert hashlib.sha256(raw).hexdigest() == digest
        path = linux_runtime / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != raw:
            path.write_bytes(raw)
        assert path.read_bytes() == raw
linux_seconds = time.monotonic() - started
print(json.dumps(dict(stage='WSL_FIRST_SYNC_MEASURED', seconds=round(linux_seconds, 3))), flush=True)
code, repeated = native_run()
assert code == 0 and repeated['source_files_written'] == 0 and repeated['source_files_reused'] == len(manifest)
lean_name = next(n for n in manifest if n.startswith('project/ElevenSquare/') and n.endswith('.lean'))
(native_runtime / lean_name).write_bytes(b'-- altered disposable source fixture\n')
code, repaired = native_run()
assert code == 0 and repaired['source_files_written'] == 1
assert hashlib.sha256((native_runtime / lean_name).read_bytes()).hexdigest() == manifest[lean_name]
inventory_before = (native_runtime / 'last-extracted-source-manifest.json').read_bytes()
code, failure = native_run('0' * 64)
assert code != 0 and 'Archive path differs' in failure
assert (native_runtime / 'last-extracted-source-manifest.json').read_bytes() == inventory_before
for name, digest in manifest.items():
    assert hashlib.sha256((native_runtime / name).read_bytes()).hexdigest() == digest
    assert hashlib.sha256((linux_runtime / name).read_bytes()).hexdigest() == digest
p = dict(status='EXACT_SOURCE_SYNC_COMPARISON_AND_BYTE_BINDING_CONTROLS_PASSED',
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), archive=str(archive), archive_sha256=expected,
         helper_source_sha256=hashlib.sha256(a.helper.read_bytes()).hexdigest(),
         verified_members=len(manifest), native_first_seconds=first['total_seconds'],
         linux_first_seconds=round(linux_seconds, 3), native_repeat_seconds=repeated['total_seconds'],
         measured_native_gain=first['total_seconds'] < linux_seconds,
         native_first_sync=first, native_repeat_sync=repeated,
         corrupted_fixture_source_restored_to_exact_archive_bytes=True,
         different_archive_digest_rejected_before_mutations=True,
         every_fixture_file_matches_manifest=True, production_source_workspaces_changed=False,
         lean_processes_started=0, proof_receipts_created=0, full_case_audits_pending=True)
record.write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps({k:v for k,v in p.items() if k not in ['native_first_sync','native_repeat_sync']}), flush=True)
