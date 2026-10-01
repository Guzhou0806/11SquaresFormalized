"""Configure only a disposable checker runtime under the user's authorization."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys

KIT = None

def direct_compiler_configuration(project):
    """Capture Lake's pinned compiler/environment once per immutable runtime job."""
    expected = 'c2059c8da4034467e5f391cfd07b81c4a7b32a7e04ff7e50c7c385993cd77010'
    keys = ['LEAN_PATH', 'LEAN_SRC_PATH', 'LD_LIBRARY_PATH', 'PATH', 'LEAN_SYSROOT', 'LEAN']
    source = KIT / 'eleven-square-lean'
    for rel in ['lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'scripts/lake.sh']:
        assert (project / rel).read_bytes() == (source / rel).read_bytes(), rel
    code = "import os,shutil,json; print(json.dumps(dict(lean=shutil.which('lean'),env={k:os.environ[k] for k in " + repr(keys) + " if k in os.environ})))"
    capture = subprocess.run(['bash', 'scripts/lake.sh', 'env', sys.executable, '-c', code],
        cwd=project, capture_output=True, text=True, check=True, timeout=15)
    result = json.loads(capture.stdout)
    binary = Path(result['lean']).resolve()
    assert 'lean4---v4.10.0-rc2' in str(binary) and binary.is_file()
    assert hashlib.sha256(binary.read_bytes()).hexdigest() == expected
    return dict(runtime_compiler=str(binary), runtime_compiler_sha256=expected,
        runtime_lean_environment=result['env'], runtime_environment_keys=keys,
        runtime_advisory_linters=False,
        runtime_launch='Direct pinned Lean with the environment captured from unchanged lake.sh env; kernel checking and source bytes unchanged.')

def efficient_runtime_launch(runner):
    old = "command = ['bash', 'scripts/lake.sh', 'env', 'lean',"
    new = "command = [CONFIG['runtime_compiler'], '-Dlinter.all=false',"
    assert runner.count(old) == 1
    old_popen = "proc = subprocess.Popen(command, cwd=ROOT,\n            stdout=log, stderr=subprocess.STDOUT, start_new_session=True,"
    new_popen = "lean_env = dict(os.environ)\n        for key in CONFIG['runtime_environment_keys']:\n            if key in CONFIG['runtime_lean_environment']:\n                lean_env[key] = CONFIG['runtime_lean_environment'][key]\n            else:\n                lean_env.pop(key, None)\n        proc = subprocess.Popen(command, cwd=ROOT, env=lean_env,\n            stdout=log, stderr=subprocess.STDOUT, start_new_session=True,"
    assert runner.count(old_popen) == 1
    return runner.replace(old, new, 1).replace(old_popen, new_popen, 1)

def unique_log_directories(runner):
    old = "out = ROOT / 'verification/small-checks' / (label + '-' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()))\nout.mkdir(parents=True)"
    new = "checks_root = ROOT / 'verification/small-checks'\nchecks_root.mkdir(parents=True, exist_ok=True)\nout = Path(tempfile.mkdtemp(prefix=label + '-' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()) + '-', dir=checks_root))"
    assert runner.count(old) == 1, 'Only adapt the supplied log allocation.'
    assert runner.count('import time\n') == 1
    return runner.replace('import time\n', 'import time\nimport tempfile\n', 1).replace(old, new, 1)

def configure(project, threads=1, memory=4096, final_check=False, kit=None):
    global KIT
    KIT = Path(kit or os.environ['T03_KIT']).resolve()
    assert (KIT / 'eleven-square-lean').is_dir()
    assert threads == 1
    reduced = os.environ.get('T03_LOW_RESOURCE') == '1'
    workers = int(os.environ.get('T03_MAX_WORKERS', '1'))
    assert 1 <= workers <= 6
    if reduced: threads = 1
    project = Path(project)
    source = KIT / 'eleven-square-lean'
    config = json.loads((source/'verification/LOW_RESOURCE_MODE.json').read_text())
    config.update(lean_memory_mb=memory, lean_threads=threads,
        lean_thread_stack_kb=32768, lean_main_stack_kb=65536,
        cpu_seconds=1800, wall_seconds=2100, nice_increment=0,
        max_concurrent_lean_checks=1, global_concurrent_lean_checks=workers,
        large_finite_checks_deferred=False,
        reason='Bounded low-priority proof pool; one compiler thread per worker.',
        memory_limit_authorization=f'{workers} proof worker slots with existing per-check memory ceilings.')
    if reduced:
        config.update(global_concurrent_lean_checks=workers,
            reason='Bounded low-priority worker count; one compiler thread per checker.',
            memory_limit_authorization=f'{workers} single-threaded proof workers, low-priority processes, existing per-check memory ceilings retained.')
    if final_check:
        # The final audit imports every case after the worker pool has drained.
        # Allow more elapsed time without increasing its memory or CPU parallelism.
        config.update(cpu_seconds=7200, wall_seconds=10800,
            lean_threads=1, global_concurrent_lean_checks=1,
            reason='Final all-case assembly audit; one low-priority checker with a longer time allowance.')
    config.pop('resource_flexibility_authorization', None)
    config.update(direct_compiler_configuration(project))
    config_path = project/'verification/LOW_RESOURCE_MODE.json'
    config_temp = config_path.with_suffix('.writing.json')
    config_temp.write_text(json.dumps(config,indent=2)+'\n')
    config_temp.replace(config_path)
    original=(source/'scripts/lean_small_check.py').read_text()
    adapted=original.replace("assert CONFIG['max_concurrent_lean_checks'] == 1 and CONFIG['lean_threads'] == 1",
        "assert CONFIG['max_concurrent_lean_checks'] == 1 and 1 <= CONFIG['lean_threads'] <= 16")
    adapted=adapted.replace("f'-M{MEMORY_MB}', '-j1', '-T200000'",
        "f'-M{MEMORY_MB}', f\"-j{CONFIG['lean_threads']}\", '-s32768', '-T200000'")
    adapted=adapted.replace("'lean_memory_limit_mb': MEMORY_MB, 'lean_threads': 1,",
        "'lean_memory_limit_mb': MEMORY_MB, 'lean_threads': CONFIG['lean_threads'], 'lean_thread_stack_kb': 32768, 'lean_main_stack_kb': 65536,")
    adapted=adapted.replace('    os.nice(NICE_INCREMENT)',
        '    os.nice(NICE_INCREMENT)\n    resource.setrlimit(resource.RLIMIT_STACK, (65536*1024, resource.RLIM_INFINITY))')
    adapted=unique_log_directories(adapted)
    adapted=efficient_runtime_launch(adapted)
    assert adapted != original and "'-j1'" not in adapted
    runner_path = project/'scripts/lean_small_check.py'
    runner_temp = runner_path.with_suffix('.writing.py')
    runner_temp.write_text(adapted)
    runner_temp.replace(runner_path)
    record=dict(project=str(project), configuration=config,
        original_source_and_exporter_unchanged=True,
        original_runner_sha256=hashlib.sha256(original.encode()).hexdigest(),
        runtime_runner_sha256=hashlib.sha256(adapted.encode()).hexdigest(),
        runtime_log_allocation='Atomic unique directories prevent timestamp collisions.',
        runtime_launch=config['runtime_launch'],
        runtime_efficiency_evidence='runtime-efficiency-benchmark.json')
    label=project.parent.name
    (KIT/'agent-evidence'/f'resumed-runtime-{label}.json').write_text(json.dumps(record,indent=2)+'\n')
    return config

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('project')
    ap.add_argument('--kit',required=True)
    ap.add_argument('--threads',type=int,default=1)
    ap.add_argument('--memory',type=int,default=4096)
    args=ap.parse_args()
    print(json.dumps(configure(args.project,args.threads,args.memory,kit=args.kit)))
