"""Exact-byte native synchronization for a locked disposable D: Lean workspace.

Creates no proof receipts and runs no Lean. The original handoff checker still
validates every actual source closure, object hash, declaration and axiom audit.
"""
from pathlib import Path, PurePosixPath
import argparse, ctypes, datetime, hashlib, json, os, sys, time, zipfile

ap = argparse.ArgumentParser()
ap.add_argument('--scratch-root', type=Path, required=True)
ap.add_argument('--main-receipts', type=Path)
ap.add_argument('--object-root', type=Path)
ap.add_argument('--other-object-root', type=Path)
ap.add_argument('--archive', type=Path, required=True)
ap.add_argument('--runtime', type=Path, required=True)
ap.add_argument('--expected-sha256', required=True)
ap.add_argument('--skip-receipts', action='store_true')
a = ap.parse_args()
assert sys.platform == 'win32', 'Native synchronization requires Windows'
scratch = a.scratch_root.resolve()
runtime = a.runtime.resolve()
assert a.skip_receipts or (a.main_receipts and a.object_root and a.other_object_root), 'Supply all receipt/object roots or use the isolated fixture option'
assert runtime.parent == scratch / 'grouped-source-runtimes'
workers = {'primary','independent-probe','helper-probe','auxiliary-probe',
           'library-a','library-b','library-c','library-d','library-e','library-f',
           'extra-a','extra-b','extra-c','extra-d','extra-e','extra-f',
           'validation-source-sync','validation-source-sync-linux'}
assert runtime.name in workers
assert not a.skip_receipts or runtime.name.startswith('validation-source-sync')
kernel = ctypes.WinDLL('kernel32')
kernel.GetCurrentProcess.restype = ctypes.c_void_p
kernel.SetPriorityClass.argtypes = (ctypes.c_void_p, ctypes.c_ulong)
kernel.SetProcessAffinityMask.argtypes = (ctypes.c_void_p, ctypes.c_size_t)
handle = kernel.GetCurrentProcess()
assert kernel.SetPriorityClass(handle, 0x4000)
assert kernel.SetProcessAffinityMask(handle, 1 << (min(os.cpu_count() or 1, 64) - 1))
def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        while block := f.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()
assert len(a.expected_sha256) == 64 and all(c in '0123456789abcdef' for c in a.expected_sha256)
started = time.monotonic()
assert sha(a.archive) == a.expected_sha256, 'Archive path differs from the exact archive opened by the WSL caller'
project = runtime / 'project'
runtime.mkdir(parents=True, exist_ok=True)
inventory = runtime / 'last-extracted-source-manifest.json'
removed = written = reused = byte_count = 0
with zipfile.ZipFile(a.archive) as z:
    manifest = json.loads(z.read('source-sync-manifest.json'))
    assert len(z.namelist()) == len(set(z.namelist()))
    assert set(z.namelist()) == set(manifest) | {'source-sync-manifest.json'}
    for name in manifest:
        rel = PurePosixPath(name)
        assert not rel.is_absolute() and '..' not in rel.parts
        assert ':' not in name and '\\' not in name
        assert rel.parts[0] == 'project' or len(rel.parts) == 1
    if inventory.exists():
        previous = json.loads(inventory.read_text(encoding='utf8'))
        root = (project / 'ElevenSquare').resolve()
        for name, expected in previous.items():
            if name in manifest or not (name.startswith('project/ElevenSquare/') and name.endswith('.lean')):
                continue
            path = runtime / name
            assert path.resolve().is_relative_to(root), ('Unexpected obsolete source path', str(path))
            if path.is_file() and not path.is_symlink() and sha(path) == expected:
                path.unlink()
                removed += 1
    for name, expected in manifest.items():
        raw = z.read(name)
        assert hashlib.sha256(raw).hexdigest() == expected, ('Manifest member mismatch', name)
        path = runtime / name
        assert path.resolve().is_relative_to(runtime)
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.is_file() or sha(path) != expected:
            path.write_bytes(raw)
            written += 1
        else:
            reused += 1
        assert sha(path) == expected, ('Runtime source byte mismatch', name)
        byte_count += len(raw)
    saved = inventory.with_suffix('.writing.json')
    saved.write_text(json.dumps(manifest) + '\n', encoding='utf8')
    saved.replace(inventory)
source_seconds = time.monotonic() - started
copied_receipts = preserved_receipts = 0
if not a.skip_receipts:
    assert a.main_receipts and a.object_root and a.other_object_root
    main = a.main_receipts.resolve()
    objects = a.object_root.resolve()
    other_objects = a.other_object_root.resolve()
    cache = project / 'verification' / 'handoff-cache'
    cache.mkdir(parents=True, exist_ok=True)
    for name in manifest:
        if not (name.startswith('project/ElevenSquare/') and name.endswith('.lean')):
            continue
        module = name[len('project/'):].removesuffix('.lean').replace('/', '.')
        receipt = main / (module + '.json')
        current = cache / receipt.name
        current_raw = current.read_bytes() if current.is_file() else None
        receipt_raw = receipt.read_bytes() if receipt.is_file() else None
        if current_raw is not None and (receipt_raw is None or current_raw == receipt_raw):
            preserved_receipts += 1
            continue
        if current_raw is None:
            if receipt_raw is not None:
                current.write_bytes(receipt_raw)
                copied_receipts += 1
            continue
        if module.startswith('ElevenSquare.Tasks.T03.'):
            obj = objects / Path(*module.removeprefix('ElevenSquare.Tasks.T03.').split('.')).with_suffix('.olean')
        else:
            obj = other_objects / Path(*module.split('.')).with_suffix('.olean')
        object_sha = sha(obj) if obj.is_file() else None
        if json.loads(current_raw).get('object_sha256') == object_sha:
            preserved_receipts += 1
            continue
        if receipt_raw is not None and json.loads(receipt_raw).get('object_sha256') == object_sha:
            current.write_bytes(receipt_raw)
            copied_receipts += 1
assert sha(a.archive) == a.expected_sha256, 'Archive changed during native synchronization'
p = dict(status='EXACT_NATIVE_SOURCE_AND_PROVISIONAL_GENUINE_RECEIPT_SYNC_COMPLETE',
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), runtime=str(runtime),
         archive=str(a.archive), archive_sha256=a.expected_sha256,
         verified_members=len(manifest), verified_source_bytes=byte_count,
         source_files_written=written, source_files_reused=reused, obsolete_matching_sources_removed=removed,
         source_sync_seconds=round(source_seconds, 3), total_seconds=round(time.monotonic() - started, 3),
         genuine_receipts_copied=copied_receipts, existing_genuine_receipts_preserved=preserved_receipts,
         proof_receipts_created=0, lean_processes_started=0,
         supplied_checker_still_validates_sources_objects_and_actual_proofs=True)
(runtime / 'native-source-sync.json').write_text(json.dumps(p, indent=2) + '\n', encoding='utf8')
print(json.dumps(p), flush=True)
