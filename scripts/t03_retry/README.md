# Experimental T03 retry tools

These portable copies record operational retries for unfinished cases 1464
and 1465. The live originals produced the actual dependency-group audits in
`verification/t03-case1464-parallel-retry.json` and
`verification/t03-case1465-operational-retry.json`. Parameterized copies have
Python source validation; they have not been replayed in Lean. They do not add
a completed case or replace the repository's serial `scripts/verify.py`.

The tools require an existing T03 checker kit with `eleven-square-lean/` and
`agent-evidence/`, exact source transports, a compatible pool dispatcher, and
genuine source/object receipts. The pending cases 1464 and 1465 generated source
closures
are not included in this Git checkpoint. These scripts alone cannot reproduce
their complete proofs.

| Tool | Role |
| --- | --- |
| `regroup_packed_case_by_depth.py` | Regroup an existing exact cold-source plan by dependency depth, with up to 64 modules and 8 MiB of source per group. Preserve earlier plans; optionally retain an exact original helper with no grouped ancestor. |
| `queue_parallel_case_retry.py` | Hold the full-case retry, let the active compiler finish, retire its serial wrapper at a compiler boundary, and retain the original sources, transport and receipts. |
| `parallel_packed_case_producer.py` | Create bounded exact-source group transports, prioritize ready groups on the longest remaining dependency path, and release the full case only after all required group audits and genuine source/object receipts match. |
| `run_independent_probe.py` | Run one supplied serial checker in an allocated worker slot, with hash-verified source extraction into a separate scratch workspace. |
| `scheduling.py` | Pure full-case/fair-group priority and aggregate-refresh deferral policies; read-only dispatch-delay observation CLI. The caller must validate readiness, source reservations, worker ownership and its concurrency ceiling. |
| `queue_failed_binding_pilot.py` | Copy exact failed binding data into an isolated pilot and queue it through the supplied source packer and existing pool; diagnostic rational equality does not accept the proof. |
| `prepare_coordinate_binding_retry.py` | Require accepted exact-data pilot evidence, rewrite only those failed proof constructions, verify an immutable retry archive, then update the single canonical grouped source. |
| `publish_coordinate_binding_retry.py` | Verify the prepared immutable retry, preserve its old guard, and queue it through an existing Linux dispatcher with no active job for that case. |
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
target audits remain pending. This operational snapshot had 155/173 published
complete cases; subsequent accepted case supplements are tracked in T03_PROGRESS.md.

The latest operational update keeps the full published count at **156/173**.
Case1465 has two independently inspected group audits and a retained exact
original `DistanceCollision` import; neither grouped case is fully accepted.
Use repeatable `--preserve-original-module MODULE` on the depth planner to
retain such a helper. It rejects helpers that import a grouped ancestor and
preserves the preceding plan before regrouping.

The public scheduling module contains policy functions rather than a pool
controller. Integrate its priority only after the caller's ordinary readiness
and receipt checks. Its aggregate-refresh predicate defers only dispatcher
group-completion rescans while full cases remain unfinished; individual audit,
receipt and execution records must always be retained. The read-only CLI takes
`--events`, `--cut`, optional `--snapshot`, and `--window` (default 20). Its
observations describe scheduling and polling delays, not Lean compiler timing.

The latest case1372 checkpoint supplies an actually accepted two-binding pilot
and an immutable full retry, not a complete case certificate. The pilot tool
requires `--kit` and `--packer`, an existing compatible kit source packer that
accepts `TASK --named`. It creates a source/task/queue candidate; only the
unchanged supplied Lean checker can accept it. The packer must use that kit's
evidence and source directories. It is not included in these experimental tools.

The preparation tool requires `--kit` and `--scratch-root`; optionally supply
`--transport-dir` and `--failed-execution` (an existing execution-record filename).
It requires a matching actual accepted pilot record and the tested exact helper
hash. It preserves the old archive, changes only the checked failed proof
constructions plus the helper import, verifies every output member, and updates
the single canonical grouped source only after all validations. It refuses a
case with an active full-case or library job. This is a source preparation action,
not a proof acceptance step.

The queue publisher requires `--kit` and optionally `--transport-dir`,
`--dispatcher-name` and `--max-workers` (default one, maximum six, matching the
prepared record). It uses Linux process control to pause only the existing
controller while replacing the case's preserved reuse guard. It refuses active
jobs for that case, and resumes the controller in a `finally` block. It neither
creates a dispatcher nor launches a compiler. All three tools have Python
source/help validation and bounded fixtures, not a portable Lean/pool replay.

`rewrite_generated_rfl.py` is a source-only helper for these exact generated
proof files. Supply `--source`, its exact `--source-sha256`, and a fresh
`--output`. It performs the same lexical tactic replacement as the verified
49-module retry, adds the tested helper import, and preserves numeric tokens.
It is not a general Lean parser: use only reviewed generated source templates.
It refuses a wrong input hash, repeated rewriting and an existing output.
Every resulting declaration still requires the original kernel check.

`share_completed_receipts.py` is a Linux copier with explicit `--runtime-root`,
optional `--scratch-root`, `--destination`, `--object-root`, repeated `--worker`
and `--once` arguments. Defaults include the separate primary scratch donor.
It copies existing receipt bytes only when the current object hash matches;
the unchanged original checker must independently validate source closure
and objects before reuse. A process lock and atomic JSON replacement avoid
concurrent partial writes. No compiler or pool is created. Only isolated
Python fixtures were replayed for this portable copy, not the production service.
