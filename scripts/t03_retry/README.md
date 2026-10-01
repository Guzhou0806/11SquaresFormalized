# Experimental T03 retry tools

These portable copies record the operational retry used for unfinished case
1464. The live originals produced the actual dependency-group audit described
in `verification/t03-case1464-parallel-retry.json`. Parameterized copies have
Python source validation; they have not been replayed in Lean. They do not add
a completed case or replace the repository's serial `scripts/verify.py`.

The tools require an existing T03 checker kit with `eleven-square-lean/` and
`agent-evidence/`, exact source transports, a compatible pool dispatcher, and
genuine source/object receipts. The pending case1464 generated source closure
is not included in this Git checkpoint. These scripts alone cannot reproduce
its complete proof.

| Tool | Role |
| --- | --- |
| `regroup_packed_case_by_depth.py` | Regroup an existing exact cold-source plan by dependency depth, with up to 64 modules and 8 MiB of source per group. Preserve the earlier plan. |
| `queue_parallel_case_retry.py` | Hold the full-case retry, let the active compiler finish, retire its serial wrapper at a compiler boundary, and retain the original sources, transport and receipts. |
| `parallel_packed_case_producer.py` | Create bounded exact-source group transports, prioritize ready groups on the longest remaining dependency path, and release the full case only after all required group audits and genuine source/object receipts match. |
| `run_independent_probe.py` | Run one supplied serial checker in an allocated worker slot, with hash-verified source extraction into a separate scratch workspace. |
| `configure_runtime.py` | Configure only a disposable runtime: pin the exact compiler/environment, use one Lean thread, and allocate unique check-log directories. |

Every machine path is supplied explicitly. `--kit` identifies the checker kit;
`--runtime-root` identifies its configured compiler/object runtime;
`--scratch-root` identifies an existing directory with space for disposable
source workspaces and preserved completed transports. `--transport-dir` defaults
to the kit's parent. The producer also requires `--receipt-root` and
`--object-root`. Its object root is the directory corresponding to
`ElevenSquare.Tasks.T03` in the shared object cache.

The queue transition, runtime configurator, and worker wrapper use Linux process
and file-lock APIs. The planner and producer support Windows or Linux. Python
3.10 or newer is required. Preparation uses low process priority and one
available CPU. The portable worker default is one; `--max-workers` can record
an already allocated pool ceiling up to six. The external dispatcher enforces
that ceiling and excludes duplicate jobs; these tools do not create a worker
pool. The producer defaults to at most eight live source transports.

The worker defaults to a scratch source workspace. It retains the worker lock,
checks the exact opened transport digest, verifies every extracted member, and
copies genuine checker receipts provisionally. The supplied checker must
revalidate both the source closure and object hashes before reusing a proof
object. Obsolete disposable Lean copies are removed only when their bytes match
the saved prior manifest. Canonical source files and input archives remain.

`configure_runtime.py` defaults to one compiler thread and a 4096 MiB per-check
ceiling; library groups use 8192 MiB through the wrapper. These are limits, not
memory reservations. It captures the unchanged pinned Lake environment once,
checks the exact compiler binary hash, and disables advisory linters in the
disposable runner. Mathematical kernel checking remains enabled. The target
HandoffAudit must still pass with the standard allowed axioms.

For arguments without starting a job, use `python3 TOOL.py --help`. Configure
paths and an existing compatible dispatcher before a transition. Runtime
manifests, process state, transport archives, logs and build caches are local
working data; retain them outside Git. Repository assembly checks remain:

```sh
python3 scripts/check_sources.py
python3 scripts/verify.py --setup
```

The actual first group passed in a disposable scratch workspace. The proposed
extra manual test found the automatic checker already running and started no
extra compiler or borrowed worker slot. Full case1464 and both public returned
target audits remain pending; the published complete-case count is 155/173.
