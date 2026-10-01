"""Reconcile historical partial metadata only after all exact targets pass."""
from pathlib import Path
import argparse,datetime,hashlib,json,re,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--handoff-log',type=Path,required=True);ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir');a=ap.parse_args()
from retry_paths import kit_paths
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
task=json.loads((K/'TASK.json').read_text());state=json.loads((E/'RESULT.json').read_text())
inventory=json.loads((E/'forward-workload-inventory.json').read_text())['records']
required={r['case'] for r in inventory};certs=state['audited_case_certificates']
assert len(required)==173 and {r['case'] for r in certs}==required
assert state['completed_case_certificates']==173
raw=a.handoff_log.read_text();assert raw.rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
execution=json.loads(a.handoff_log.with_suffix('.json').read_text());assert execution['exit_code']==0
paths=re.findall(r'Log: (/.*/handoff-HandoffAudit-[^/\s]+/lean.log)',raw);assert paths
actual=Path(paths[-1]);output=actual.read_text();check=json.loads(actual.with_name('CHECK.json').read_text())
assert check['status']=='accepted' and check['exit_code']==0
found={n:[v.strip() for v in ax.split(',') if v.strip()] for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output,re.S)}
found.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",output)})
assert set(task['axiom_targets'])<=found.keys()
assert all(set(found[n])<={'propext','Classical.choice','Quot.sound'} for n in task['axiom_targets'])
for c in certs:
    audit=(E/(c['audit']+'.log')).read_text();assert c['target'] in audit and 'sorryAx' not in audit
transport=transport_root/('.t03-runtime-sync-'+Path(execution['task']).stem+'.zip')
assert Path(execution['task']).name=='final-returned-target-task.json'
subprocess.run([sys.executable,str(E/'audit_inherited_admissions.py'),'--transport',str(transport)],check=True)
inherited=json.loads((E/'inherited-admissions.json').read_text())
assert inherited['scope']=='final audited transport'
inherited_note='\n'.join('- `'+r['declaration']+'` in `'+r['path']+'`: `'+', '.join(r['actual_axioms'])+'`.'
    for r in inherited['declarations'])
snapshot=E/'RESULT-before-final-target-verification.json'
assert not snapshot.exists(),'Do not overwrite the preserved historical result.'
snapshot.write_text(json.dumps(state,indent=2)+'\n')
# Rebuild current metadata rather than preserving stale candidate counts as
# though they described the final reachable proof closure.
final=dict(status='exact_targets_verified',release_id=task['release_id'],base_snapshot_sha256=task['base_snapshot_sha256'],
 completed_case_certificates=173,audited_case_certificates=certs,remaining_local_admission=None,
 required_target_audits_contain_sorryAx=False,export_protocol_status_source='RETURN.json in the validated return ZIP',
 target_axioms={n:found[n] for n in task['axiom_targets']},actual_target_audit_log=str(actual),actual_target_audit_sha256=hashlib.sha256(output.encode()).hexdigest(),
 final_handoff_log=str(a.handoff_log),verification_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 audited_concrete_pose_templates=48,audited_ownership_groups=16,audited_owned_vertices=107,audited_case_initializations=173,audited_generic_strict_cores=602,
 public_trace_witness='Case 1145 uses the public trace; remaining cases use a reflexive public trace after a separately checked SemanticReplay refutation.',
 inherited_admissions_in_target_closure=[],inherited_admissions_in_imported_frozen_sources=inherited['declarations'],
 inherited_admission_audit='inherited-admissions.json',historical_result_snapshot=snapshot.name,
 exporter_scope='Only the exact T03 return is claimed; this is not verification of the merged seven-task release.')
(E/'RESULT.json').write_text(json.dumps(final,indent=2)+'\n')
distance_note=''
distance_publication=E/'distance-shortcut-case1465-publication.json'
if distance_publication.exists():
    distance_record=json.loads(distance_publication.read_text())
    assert distance_record['status']=='ONE_CASE_PRIVATE_SHORTCUT_PUBLISHED_FULL_CASE_AUDIT_PENDING'
    assert distance_record['comparison']['full_statement_identical']
    distance_note='''Four groups in one case-1465 collision proof use an orientation-independent
distance argument. Strict squared-distance bounds on every pair of center-hull
vertices extend to every pair of centers by convexity of the open unit disk.
Their midpoint lies strictly inside both unit squares, so those groups need no
angle-dependent Minkowski calculation. The shared lemma and the complete
replacement collision theorem have actual clean Lean axiom audits.
'''
report=f'''# T03_Returned — exact targets verified

Release: `{task['release_id']}`.
Base snapshot: `{task['base_snapshot_sha256']}`.

All 173 returned cases have complete Lean certificate proofs. Both original
target declarations at `coverCap` pass the supplied handoff checker:
`ElevenSquare.Pending.returned_certificate_exists` and
`ElevenSquare.Pending.returned_excluded`. Their actual transitive axiom audits
use only `propext`, `Classical.choice`, and `Quot.sound`; neither target depends
on `sorryAx` or an inherited admission. This is the T03 return for integration,
not a claim that the combined seven-task release has been verified.

The frozen imported sources retain the following upstream admissions. They are
reported separately from the two T03 targets, whose actual axiom output above
shows that these admissions are unused in their proofs:

{inherited_note}

`agent-evidence/InheritedAudit.lean`, `InheritedAudit.log`,
`InheritedAudit-CHECK.json`, and `inherited-admissions.json` preserve the actual
declaration output, the accepted elaboration check, and the frozen source hashes.
An accepted elaboration check of an admitted declaration does not verify it.

## Proof

The initialization library proves the 48 reused pose templates, 16 ownership
groups, 107 owned vertices, and all 173 exact case bindings. All 602 strict
angular cores are justified on their complete closed intervals. Each row uses
a directly proved convex-hull cover with checked integer Farkas certificates.
Necessary self-hull cuts keep their ownership hypotheses. Core, old, and mixed
point witnesses establish the chosen points, and exact state bindings preserve
the recorded downstream hulls. Universal collision proofs quantify over every
compatible partner pose, including closed interval endpoints and all required
ancestors. Hashes and Python calculations only propose proof data; Lean checks
every mathematical obligation used by the targets.

Case 1145 composes the frozen public `VerifiedTrace` constructors. The other
cases use the private `SemanticReplay` relation and its proved soundness to
compose actual state transitions and derive an occupancy contradiction from
a terminal empty row. After that contradiction is proved,
`certificate_of_charted_refutation` supplies the same empty terminal state at
both endpoints of a reflexive public `VerifiedTrace`. The initialization
implication follows from the proved contradiction. Thus that existential public
witness is a zero-step trace; the geometric reasoning is checked in the separate
semantic replay. The exact public types remain unchanged and the exclusion is
not assumed in its own proof.

## Simplification and checks

The proof shares initialization templates, polygons, cores, repeated geometric
covers, and collision bands. Indexed witnesses avoid repeated list membership
calculations; linear partner-row subset proofs avoid quadratic elaboration.
Exact named entries make large hull lists manageable without changing their
points, planes, factors, or geometric claims. All cases are organized in the
12 original batches, and the final assembly checks the exact returned-index
binding. Slower diagnostic alternatives were not adopted.

{distance_note}
For concrete Boolean certificates, a private tactic constructs the ordinary
`Eq.refl true` proof term directly. Lean's declaration kernel still checks the
entire Boolean reduction; the tactic avoids a duplicate elaborator reduction.
The paired geometry pilot passed all its axiom audits, and an actual negative
control was rejected by the pinned kernel for claiming `false = true`.

Lean is pinned to 4.10.0-rc2, with mathlib revision
`3fef63ff3bda38478ba4364ff03999f0246745a2`. The user lifted the packet's resource
limits. After a storage pause, the user requested lower resource usage. The later
case checks initially used four single-threaded workers at lower process
priority, then six workers on six CPU cores after the user's urgent completion
request. `urgent-six-worker-transition.json` records adoption of the existing
checks without restarting them. Source preparation ran serially. The final target
check ran serially as well. Per-check memory limits and actual final
execution settings are recorded in the audit evidence.
The supplied checker, exporter, public source contracts, data, and pinned
toolchain are preserved. Reused compiler objects require genuine receipts
matching both source dependency hashes and object hashes. The return contains
source and audit evidence, with no compiler objects or dependency caches.
Disposable runtime logging uses atomic unique directory names after an earlier
timestamp collision interrupted case 2047. Its queued retry retained identical
task, proof, compiler, and environment bytes. The runtime change affects only
log allocation; `runtime-log-collision-fix.json` records that change.
Later disposable runtimes invoked the identical pinned compiler directly with
the environment captured from the unchanged Lake launcher, and disabled
advisory linters. Proof sources, kernel checking, and the supplied handoff
checker were unchanged. One identical-source comparison took 7.98 seconds
through Lake and 6.46 seconds with the runtime adjustment; this is a sample,
not a general speedup claim. The adjusted runner accepted the same clean
axiom audit and the kernel rejected a deliberately false Boolean equality.
`runtime-efficiency-benchmark.json`, `runtime-efficiency-application.json`,
and the positive and negative compiler logs preserve that evidence.
A bounded object-cache layout experiment improved file-access microbenchmarks
but showed no clear end-to-end improvement in two paired checks of an identical
geometric proof. It was not adopted. `cache-lean-benchmark-retry01.json` and its
four actual compiler logs preserve the clean audits and measured times. The
original cache remained intact and the temporary mount was closed.
A further collision-specific comparison took 25.68 seconds with ordinary
`rfl` and 13.32 seconds with `t03_bool_refl`, with identical mathematical
statements and clean actual axiom audits. The tactic constructs `Eq.refl true`;
Lean's declaration kernel still validates the complete Boolean computation.
Separate optimized helpers were added selectively to unchecked collision
proofs in idle cases, preserving canonical helpers and all proof data. The
supplied checker subsequently audited the complete cases and exact targets.
`collision-bool-benchmark.json` and per-case publication records preserve this
change. The paired timing is a sample, not a general speedup claim.
Eight identical homogeneous-coordinate equality proofs took 7.04 seconds
with ordinary reflexivity and 4.37 seconds when the ordinary `Eq.refl` proof
term was constructed from the equality's right-hand expression. The declaration
kernel still checked equality with the left-hand expression, and rejected a
deliberately false rational equality. Exact theorem types, proof equality,
numeric data, and clean axiom audits were preserved. This construction was
applied only to selected unchecked copied coordinate binding proofs; the
already published or running grouped source closures remained unchanged.
`equality-refl-benchmark.json`, its actual positive/negative compiler logs,
and `case1393-equality-refl-publication.json` retain the bindings and evidence.
During source preparation, the dispatcher excluded only the case being prepared
and continued refilling other worker slots. Its six-slot limit was unchanged;
`nonblocking-optimization-dispatcher-transition.json` records that revision.
The large case 1393's optimized collision dependencies were initially divided
into 305 small exact-source audit batches. This earlier queue was superseded
by the bounded grouped sources described below, preserving its completed
objects, genuine receipts, source bindings, and actual compiler logs.
`case1393-optimized-backfill-preparation.json` binds the batch sources to the
earlier case archive. The complete case and final public targets were audited
separately; dependency checks did not count as complete case certificates.

An eight-module paired check took 51.30 seconds as separate files and 29.19
seconds with the same proof bodies in one module. Proof equality and clean
axiom audits were checked by Lean. The unfinished portion of case 1646 was
therefore grouped into 46 bounded modules. Its first grouping exposed a real
duplicate-name conflict when importing an original shared proof alongside it;
that attempt was retired after its current compiler finished. The replacement
gives copied private declarations separate names, preserves all numeric tokens,
and proves the original certificate through an identical original type header.
`packed-compilation-benchmark.json`, the failed and corrected import tests,
and `case1646-packed-namespaced-publication.json` retain this evidence. The
complete certificate and both public targets received their own actual checks;
grouping itself was not a proof acceptance criterion.

The largest remaining case, 1393, used 523 groups arranged by dependency depth.
The 214 initially independent groups could use the existing worker slots in
parallel. Ready groups were prioritized by their longest remaining dependency
path so sequential replay work could overlap independent leaves. An archive
producer restart revalidated every existing immutable transport and genuine
receipt, preserving running proof checks. The same grouping approach was also
applied to queued case 1311, reducing 3,399 unchecked files to 54 groups.
Its first grouped attempt failed eight retained-coordinate reflexivity proofs.
An isolated Lean probe checked the same eight homogeneous-coordinate lists and
retained polygons with ordinary reflexivity and the kernel equality helper;
both succeeded with only propext. The retry changed only those eight proof
constructions and added the helper import, preserving every numeric token and
the earlier accepted groups. Its original failed transport and compiler logs
were retained. The exact full-case certificate still required its own audit.
Future grouped preparations used the same checked equality construction.
Case 1372's first grouped attempt failed two coordinate reflexivity proofs.
The original supplied checker accepted an isolated pilot with the exact retained
and homogeneous coordinate data and the checked equality construction. Both
actual axiom outputs contained only propext. The full retry changed only those
two proof constructions and the helper import, preserving the earlier accepted
groups and every numeric token. The failed source transport was preserved;
the complete case and public target audits were still independently required.
The pilot audit, CHECK.json and immutable retry bindings are retained in
the case1372-coordinate-binding-pilot and retry evidence.
Its subsequent Chunk009 also failed large row/state and coordinate reflexivity
goals. A distinct retry replaced the remaining ordinary reflexivity proof
constructions with the tested Eq.refl helper, preserving every statement and
numeric token and the accepted first nine chunks. The supplied kernel still
checked each changed declaration and the complete exact case target. The
genuine receipt copier was extended to disposable scratch source workspaces so
completed chunks could be reused after a later failure; it created no receipts,
and the original checker still validated source closure and object hashes.
Case 1464's remaining 19,662 unchecked modules were arranged into 370 groups
at 91 dependency levels, with 151 groups initially independent. Its serial
checker retired after its current compiler finished. Registered receipts and
objects were preserved, and the original checker revalidated every reused
object. The new parallel retry retained the exact certificate statement and
every numeric token. Its disposable source workspaces used D: to limit C:
growth; the pinned compiler, supplied checker and six-worker limit remained.
`case1464-packed-parallel-publication.json` and
`case1464-parallel-retry-transition.json` preserve that transition.
Two issued case-1464 dependency groups subsequently failed reflexivity of large
collision-band row lists. Their original failed transports and compiler logs
were preserved. Distinct retry task names repaired those two groups, and the
same ordinary equality construction was applied only to never-issued groups.
All other issued or running source closures, original statements and numeric
data stayed unchanged. The source producer was checkpointed at a completed
file-publication boundary; no Lean process was stopped. The full-case guard
remained until every actual dependency audit and matching receipt passed.
Case 1465 had 12,841 cold modules: 12,840 generated modules were grouped into
253 chunks at 82 dependency levels, with 87 initially independent groups.
The exact original DistanceCollision mathematical helper remained imported
unchanged; it had no grouped ancestor and received normal checker validation.
Two source-packing grammar prechecks were resolved before output generation;
neither was a failed Lean proof check. The exact certificate type and all
numeric tokens were preserved. `case1465-packed-parallel-publication.json`,
`case1465-parallel-retry-transition.json`, and
`case1465-packed-preparation-prechecks.json` retain this evidence.
Two subsequently issued case-1465 groups failed large equality elaborations.
The preserved-closure repair changed those failed groups and never-issued
groups, keeping every other published dependency unchanged. Their distinct
retry names and immutable original failed transports are recorded separately.
Case 1731 also failed in its tenth packed group. Its retry preserved the nine
already accepted groups and all exact theorem statements and numeric tokens,
and replaced 8,928 remaining ordinary equality proof constructions at once.
Every changed declaration still required the supplied Lean kernel and the
complete original certificate axiom audit before case acceptance.
Case 1499's original grouped check failed Chunk026 after 26 accepted batches.
Those accepted source bytes were retained unchanged. The remaining 3705 exact
declaration bodies were regrouped into 72 private modules at 22 dependency
levels instead of 58 serial batches; ordinary equality construction changed
6770 times while all statements, numeric tokens and the original target bridge
were preserved. The first regrouped dependency received an actual clean target
audit; full-case acceptance independently required the original target audit.
The remaining-parallel source/plan/publication records bind this transition.
Case 2069's remaining 4,314 unchecked modules were arranged into 120 groups
at 69 dependency levels, with 25 groups initially independent. The original
serial checker retired only after its current compiler finished. Existing
registered receipts and objects were preserved; the fresh grouped retry retained
the exact original certificate statement and all numeric tokens. Its source
workspaces used D: and its checks stayed within the same six-slot pool.
The original external-source reuse hold was preserved in a separate record;
its removal from the active local case did not accept the external reported
proofs. The parallel publication and compiler-boundary transition retain the
source digests and distinguish the deliberate exit 130 from a mathematical
failure or an accepted full-case certificate.
At most eight ready chunk transports per producer were retained on C:; accepted
transports were preserved on D: after checking their actual execution digests.
Every group required both the supplied checker's exact target audit and a
genuine matching source/object receipt before the full case task was released.
The original serial helper queue was superseded after its active compilers
finished naturally. Old case-zero diagnostic queues were preserved and removed
from scheduling. Neither change increased the six-worker limit. The original
canonical source files and numeric data remained unchanged.
The dispatcher gave ready cases with fewer active group checks a slot before
choosing their longest remaining dependency path. Controller adoptions left
running proof workers unchanged and interrupted no Lean compiler. Group jobs
retained their individual actual evidence without rescanning the complete audit
history; every full-case completion and manual refresh still rebuilt it.
The later dispatcher rotates the oldest waiting case between equally occupied
cases and chooses the longest dependency path within that case. Simultaneous
slot assignments update case counts so one case cannot take every free slot.
The actual priority function passed starvation and simultaneous-slot scenarios.
An import-timing-only probe audited True.intro on an already checked closure;
its 48.53s audit did not beat the prior real target's 43.41s. It established no
case certificate or geometric dependency, and no actual target audit was
removed. The original full-case and two public-target audits remained required.
An abstract homogeneous polygon-fan bridge proved that integer orientation and
cleared-denominator edge checks imply the same original rational Boolean claim.
Its actual kernel check and standard-axiom audit passed. An identical 56-vertex
polygon comparison passed both proofs and a zero-denominator negative control:
the rational module took 33.28s and the integer module 34.23s, followed by a
23.11s target audit. This single sequential observation with the background pool
showed no saving, so the bridge was not applied to the pending case sources.
The experiment did not establish or count any full-case certificate.
Observed refill intervals in `dispatcher-history-refresh-efficiency.json`
include scheduling and polling and are not controlled compiler benchmarks.
The final disposable source workspace also used D: to avoid expanding the full
audited closure in WSL's C: storage. These changes did not increase concurrency
or replace any source/object receipt or proof audit.
For disposable D: workspaces, native Windows source synchronization reduced
cross-WSL file operations while retaining exact archive and every member hash.
The recorded 381-member fixture took 3.734 seconds natively versus 11.665
seconds through WSL; an unchanged repeat took 0.953 seconds. The fixture also
restored altered source bytes and rejected a different archive digest before
any mutation. Its 372 provisional receipt copies were byte-identical to actual
main checker records. No receipts were fabricated, and the original checker
still independently validated source closures and object hashes. Actual job
synchronization records preserve its scope and timings separately from Lean.
Fresh private packed sources could use authorized D: storage through a logical
module-directory junction. Windows and WSL access were checked. Final staging
copied the exact audited sources into fresh physical files, so no junction or
cache became part of the original exporter return.
The last 15 pending cases all received local check paths. Five fresh source
preparations ran serially at lower priority on one CPU core; their producers
used the existing six compiler slots. Case 1393 preserved its issued source
closures while replacing ordinary equality constructions in 462 never-issued
groups. Case 1849 used a distinct dependency-depth retry, preserving its old
archive and task. The all-pending-local-queues checkpoint binds the exact source
archives and actual first-group audit evidence. None of those preparations or
dependency batches counted as a complete case certificate.
The scheduler checked for a prepared archive before examining historical worker
logs. On the same 4361 unattempted rows, this selected the same ready tasks in
1.55 seconds instead of 15.76 seconds; the repeat took 1.54 seconds. The timing
covers source-readiness filtering only, rather than Lean compilation. The
controller then polled every five seconds, with all proof checks, reservations
and the six-worker limit retained. Its adoption interrupted no compiler.

`agent-evidence/Audit.lean` and `audit.log` preserve the exact target audit.
`final-handoff.log`, `final-handoff-execution.json`, and `audit-CHECK.json` preserve
the actual check result and resource settings. Per-case audit snapshots and
`RESULT.json` record all 173 complete cases. `staging-manifest.json` records the
reachable source hashes matched to the final audited transport. The provided
`make_return.py` performs the final ownership and source-scaffold export checks.
'''
(K/'REPORT.md').write_text(report,encoding='utf8',newline='\n')
print(json.dumps(dict(status='EXACT_TARGET_REPORT_WRITTEN_EXPORT_PENDING',targets=task['axiom_targets'],cases=173)),flush=True)
