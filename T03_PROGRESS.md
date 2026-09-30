# Returned-case common tools: partial progress

The returned family requires certificates for all 173 assigned indices.
`ElevenSquare.Pending.returned_certificate_exists` remains admitted in this
repository, and global optimality remains unfinished. This branch supplies
checked common tools and the complete source closure of one audited certificate,
case2135. It does not discharge the full-family obligation.

## Included source

`ElevenSquare/Tasks/T03/Common.lean` imports two useful improvements and their
complete local helper dependencies. The existing geometry and public interfaces
are preserved, including the stronger previously merged baseline and global
partial returns. No new admission is introduced.

- `DistanceCollision.lean` proves an orientation-independent collision rule.
  When two unit-square centers have squared distance strictly below one, their
  midpoint lies in both open squares. Convexity extends strict vertex-pair
  distance bounds to all points of the two center hulls. Positive homogeneous
  denominators turn those bounds into exact integer comparisons. The resulting
  `CollisionBand.ofUnitDistance` supplies a collision without constructing
  angle-dependent strict cores.
- `KernelBoolRefl.lean` provides `t03_bool_refl` for exact Boolean checks. It
  constructs the ordinary term `Eq.refl true` without first reducing the goal
  in the tactic elaborator. Lean's declaration kernel still validates the full
  computation. A pinned-compiler negative control rejected its attempted use
  for `false = true`; it is not a proof oracle.

The common helper closure adds 39 Lean modules, approximately 117 KiB. Its 15
existing local geometry/interface dependencies have the same Lean tokens as
the independently audited dependency snapshot. Those upstream files are not
replaced. `ElevenSquare/Progress.lean` imports this closure, and the normal target
audit now queries the six distance/collision results.

## Complete case2135 checkpoint

`ElevenSquare/Tasks/T03/Checkpoint.lean` also imports
`Batch12/Case2135/Forward/Certificate.lean`. Its theorem
`ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Certificate.certificate_exists`
has the original packing, case mask, owner permutation, initialized-state,
`VerifiedTrace`, and terminal-state type at `coverCap`.

All 723 reachable local source dependencies are included or already present in
the repository. This adds 676 dependency files and one entry-point file, totaling
15,250,955 bytes. No cache, build object, machine log, or handoff archive is
included. `verification/t03-case2135.json` records the complete source closure
and its source hashes. Existing upstream files, including the stronger merged
baseline proofs, are preserved.

The substantive geometry is a proved semantic replay ending in an empty terminal
row. Its soundness establishes the occupancy contradiction. The generic
`semantic_replay_certificate` wrapper then supplies a reflexive public trace in
an empty state; its initialization implication follows from that proved
contradiction. The public theorem type is unchanged, and the geometric replay
is proved rather than assumed.

## Audit scope

The six distance/collision declarations passed an independent compiler audit
with only `propext`, `Classical.choice`, and `Quot.sound`. The tactic was checked
with the same pinned Lean 4.10.0-rc2 toolchain and mathlib revision as this
repository. `verification/t03-progress.json` records portable declaration names,
axiom sets, and source hashes. These are reported independent checks, not a
fresh replay of the entire merged assembly.

Case2135 passed the supplied independent handoff checker and its actual target
axiom audit with only the same three standard axioms. The source archive used
for this checkpoint matches the completed check's recorded digest. The merged
GitHub assembly has not been freshly replayed in Lean; its serial verifier now
includes the case2135 target query so that a full checkout can reproduce it.

Separate ongoing work had completed full audits for 150 of the 173 case
certificates at the original progress snapshot. Case2135's complete source
closure is now supplied. The other 149 audited case source collections remain
outside this checkpoint; their declaration list is informational and supplies
no certificate proofs here.

A measurement of those 150 completed-check source manifests found 98,369
distinct Lean source files, totaling 5,350,077,814 bytes before deduplication
against the repository. The common-helper snapshot already supplied 54 of those
files, leaving 98,315 files and 5,349,623,026 bytes to add for the entire snapshot.
No conflicting source versions were found. This was a manifest-only measurement;
the full collection was not extracted, rebuilt, or published. The one-case
checkpoint keeps the added source manageable while supplying a complete proof
that can be independently replayed.

The remaining case work, assembly of both exact public returned targets, their
clean axiom audit, and the completed return package remain unfinished.

To reproduce the included source and main audit serially in a full checkout:

```sh
python3 scripts/check_sources.py
python3 scripts/verify.py --setup
```

`--all` on the verifier checks every included module. Acceptance of the six
existing admissions still means partial assembly success; see [MISSING.md](MISSING.md).
