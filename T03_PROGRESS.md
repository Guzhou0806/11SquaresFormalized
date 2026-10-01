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

The common helper closure adds 40 Lean modules, approximately 117 KiB. Its 15
existing local geometry/interface dependencies have the same Lean tokens as
the independently audited dependency snapshot. Those upstream files are not
replaced. `ElevenSquare/Progress.lean` imports this closure, and the normal target
audit now queries the six distance/collision results.

## Checked equality helper and ongoing case work

`KernelEqualityRefl.lean` adds `t03_eq_refl`, which constructs ordinary `Eq.refl`
on an equality's right-hand expression. The declaration kernel still checks
that this term proves the original equality. It avoids repeating some expensive
coordinate reductions in the tactic elaborator and imports only `Lean.Elab.Tactic`.

An independent comparison of the same eight coordinate equality proofs took
**7.039 seconds with the baseline and 4.368 seconds with the helper**, about 38%
less elapsed time in that sample. Both actual target audits contain only
`propext`, and the declaration kernel rejected its attempted proof of
`(1 : Rat) = 2`. This is a measured sample, not a whole-case completion estimate.
`verification/t03-equality-refl.json` supplies the exact helper hash, input hashes,
target axiom sets, and sanitized positive and negative check evidence. The
merged GitHub source tree has not been freshly replayed in Lean.

The accepted source checkpoint is now **156/173**, with 17 cases unfinished.
The following optimization figures describe the earlier helper benchmark snapshot.
Case1393's ongoing local source migration replaces 5,601 coordinate equality
proof expressions across 178 still unaccepted groups while preserving their
exact data. The last observed dependency progress was 37/523 groups; this is
not a full certificate audit. Neither that source collection nor case1311 is
published as an accepted case. Case1311's full grouped attempt failed eight
`homRetained_binding` reflexivity proofs and is under repair; its rational
diagnostic does not replace a Lean proof. Public target assembly and the final
return ZIP remain incomplete. Earlier accepted release assets are unchanged.

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

## Full 151-case source release

The complete exact source dependency collection for **151 independently audited
cases** is available in the [partial T03 release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited-151-20260930). This extends
the earlier 150-case snapshot with the completed case1840 certificate. Download
the [source checkpoint](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-151-source-checkpoint.zip) and [SHA-256 sidecar](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-151-source-checkpoint.zip.sha256).

The ZIP contains 101,494 reachable Lean modules and 5,499,202,925 bytes of Lean
source, compressed into a 1,518,846,009-byte asset. Its SHA-256 is
`44fa1bf800965c2b511fb52195206c7ea3849e8e3073c180fa1896860216b4ca`. Every selected original source and every finished
output member was streamed and hash-verified. Actual independent target audits
for all 151 certificates use only the three standard axioms. The pinned
dependency metadata and original supplied serial checkers are included.

The large generated collection lives in the release asset. The Git branch
continues to contain the common tools, the small case2135 checkpoint, and compact
release metadata in `verification/t03-release-checkpoint.json`. It does not put
the multi-gigabyte generated collection into normal Git history.

Extract the release checkpoint separately. It preserves the exact frozen
interfaces from the successful independent checks and should not overwrite the
stronger interfaces already merged into this repository. It contains no build
objects, machine logs, private handoff archives, account information, or chats.

At this 151-case checkpoint, 22 cases remained. The supplements below add
five complete source closures; 17 cases and the full public assembly,
combined audits, and final return ZIP remain unfinished. A fresh merged
repository Lean replay and global optimality proof are not claimed.
The source asset's README explains serial replay.

## Additional audited cases 1484 and 2122

A [standalone source supplement](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-cases1484-2122-source-supplement.zip) now supplies the complete exact
source closures of case1484 and case2122, together with their actual target-only
HandoffAudit transcripts, pinned environment metadata, and original supplied
serial checkers. The original 151-case asset is unchanged. Together these assets
publish **153 of the 173** independently audited case certificates.

The supplement contains 14,144 reachable Lean modules and 618,524,343 bytes of
Lean source in a 150,038,569-byte ZIP. Its SHA-256 is
`178d0d165a2c37fc0452b467605075f65abe6d859b5ceff0b0c400cc83b20610`; the [checksum sidecar](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-cases1484-2122-source-supplement.zip.sha256) and compact
[checkpoint metadata](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/CHECKPOINT-supplement-public.json) are also available. GitHub's
server-reported asset size and SHA-256 match the locally verified checkpoint.

Both exact full certificate targets passed their accepted independent
HandoffAudit with only `propext`, `Classical.choice`, and `Quot.sound`. Their
original execution transport digests match the preserved input archives. Every
selected original source and every output member was streamed and hash-checked;
each full source import closure was checked separately. Portable bindings are
recorded in `verification/t03-source-supplement.json` and in the archive's
individual case source manifests.

The supplement can be replayed independently without downloading the larger
151-case asset. Extract it separately, using the archive README's serial replay
instructions; preserve the stronger merged repository interfaces. It contains
source and target-only audit transcripts, with no build objects, caches, machine
logs, private handoff archives, account information, or conversation records.

At this 153-case checkpoint, 20 cases remained and case1646 was still
unfinished. Its subsequently accepted grouped closure is published below.
The public target assembly, combined audits, and final return ZIP remain
unfinished; no full T03 completion or global optimality proof is claimed.

## Accepted grouped case1646 source checkpoint

The [standalone case1646 supplement](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-case1646-source-supplement.zip) supplies its newly accepted full
source closure and target-only HandoffAudit transcript. The original 151-case
asset and the cases 1484 / 2122 supplement remain unchanged. Together the three
source assets published **154 of the 173** audited case certificates at this checkpoint.

The accepted import root is
`ElevenSquare.Tasks.T03.Batch06.Case1646.PackedNamespacedRetry01.Chunk045`.
It reexports the exact original target
`ElevenSquare.Pending.T03.Batch06.Case1646.Forward.Certificate.certificate_exists`.
That complete target passed its actual supplied HandoffAudit with only
`propext`, `Classical.choice`, and `Quot.sound`. This checkpoint contains the
accepted reachable grouped sources; the earlier unverified canonical source
chain is not substituted for them.

The archive contains 5,077 reachable Lean modules and 299,370,933 bytes of Lean
source, compressed into 72,655,539 bytes. Its SHA-256 is
`2d6aa87cbbcbae21c0a291bfc740b97b3611bdc1d3b0077b4b8396ae5c4d7ef5`. The [checksum sidecar](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-case1646-source-supplement.zip.sha256) and
[portable audit metadata](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/CHECKPOINT-case1646-public.json) are available. The exact
accepted execution transport digest, all source-member hashes, the full import
closure, and every completed output member were verified. GitHub's asset size
and SHA-256 match the locally verified ZIP.

`verification/t03-case1646-source-supplement.json` records the declaration,
grouped source root, accepted transport digest, and audit. The archive README
explains standalone serial replay. Extract it separately; preserve the stronger
merged repository interfaces. It includes exact pinned metadata, the original
supplied checkers, and a neutral one-thread replay profile. No cache, build
objects, machine logs, private transports, account information, or chats are
included.

At this 154-case checkpoint, 19 cases remained. Case2047 subsequently passed
its complete target audit and is published below. The public family assembly,
combined audits, and final return ZIP remain unfinished.

## Accepted case2047 source checkpoint

The [standalone case2047 supplement](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-case2047-source-supplement.zip) adds its complete exact source
closure and actual target-only HandoffAudit transcript. All earlier source
assets remain unchanged. Together these four source assets published
**155 of the 173** independently audited case certificates at this checkpoint.

The accepted source root is
`ElevenSquare.Tasks.T03.Batch10.Case2047.Forward.Certificate`, and its exact target
is `ElevenSquare.Pending.T03.Batch10.Case2047.Forward.Certificate.certificate_exists`.
Its supplied full HandoffAudit accepted the target in 60.34 seconds, using only
`propext`, `Classical.choice`, and `Quot.sound`. The accepted execution transport
SHA-256 is `e05fd4875a3ef90f8cf91f392849be333d04fea036bfa8e350984d7e12d55394`.

The archive contains 9,753 reachable Lean modules and 114,655,948 bytes of Lean
source in a 35,899,608-byte ZIP. Its SHA-256 is
`066c9e2bc6d29ccc24a946117f6d9b018d36d4ed667026ca40c6442020d49504`. The [checksum sidecar](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-case2047-source-supplement.zip.sha256) and
[portable checkpoint metadata](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/CHECKPOINT-case2047-public.json) are available.
Every selected archived source and finished output member was hash-checked;
the complete import graph was verified. Fourteen unused modules in the accepted
transport were excluded because they are outside this target's reachable
closure. GitHub's server-reported asset size and digest match the verified ZIP.

`verification/t03-case2047-source-supplement.json` binds the source root, exact
target, transport digest, and actual audit. The archive includes pinned
Lean/mathlib metadata, original serial checkers, and standalone replay
instructions. Extract it separately to preserve the stronger merged repository
interfaces. No new merged repository Lean replay was performed.

The exact public returned targets still require the remaining certificates,
assembly, and clean combined audits. The final return ZIP and global optimality
proof remain incomplete.

## Accepted case1848 source checkpoint

The [standalone case1848 supplement](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-case1848-source-supplement.zip) supplies the newly accepted
complete source closure. Together all five named source assets now publish
**156 of the 173** independently audited case certificates; **17 cases remain**.
All earlier source assets are unchanged.

The accepted import root is
`ElevenSquare.Tasks.T03.Batch09.Case1848.Forward.Certificate`, and its exact target
is `ElevenSquare.Pending.T03.Batch09.Case1848.Forward.Certificate.certificate_exists`.
Its actual supplied full HandoffAudit accepted the target in 90.27 seconds with
only `propext`, `Classical.choice`, and `Quot.sound`. The accepted transport
SHA-256 is `477eba64c8e24c6b3bbca4111ad2d086070c33fd01ed4d34899f0c280800b8cf`.

The archive contains 4,479 reachable Lean modules and 221,134,643 bytes of Lean
source, including the pinned Lake source, in a 42,435,321-byte ZIP. Its SHA-256 is
`ae5f57e138ca429e1d619a7abcd22791936ced830bc1fc0abab3f1f607c8fb58`. The [checksum sidecar](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/T03-audited-case1848-source-supplement.zip.sha256) and
[portable audit metadata](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-audited-151-20260930/CHECKPOINT-case1848-public.json) are also available.
Every included source and output member was hash-checked, and the full import
graph was verified. The 205 transport modules outside the accepted target's
reachable closure are excluded. GitHub's asset size and digest match the
verified checkpoint.

`verification/t03-case1848-source-supplement.json` binds the accepted execution
transport, exact declaration, source root and actual target audit. The ZIP
includes target-only audit text, exact pinned environment metadata, original
serial checkers and standalone replay instructions. Extract it separately to
preserve the stronger merged repository interfaces. No fresh merged repository
Lean replay was performed. Case1464, the remaining full certificates, assembly
and clean combined audits of both public targets, and the final return ZIP
remain unfinished.

## Case1464 operational retry checkpoint

Case1464 remains unfinished. Its retry groups 19,662 cold source modules into
370 groups across 91 dependency levels, with 151 groups initially independent.
The producer prioritizes ready groups on the longest remaining dependency path
and holds the exact full-case task until every required group audit and genuine
source/object receipt matches. The original serial checker was retired at a
compiler boundary; its current Lean process finished, and original transports,
sources, objects and registered receipts were preserved.

The grouped source archive SHA-256 is
`d1eb0da8dc2a1b467abd8a6821d5264e1e1151f8ce1952578bb40bfb935f1bdf`.
This is a local pending-source binding, not a newly published source asset.
Canonical numeric data remains unchanged. The retry changes 99,335 finite
Boolean and 8,122 coordinate equality proof constructions to the existing
kernel-checked helpers; those helper sources themselves are unchanged.

Four actual dependency-group target audits were independently inspected at
the 2026-10-01 03:08:00 UTC snapshot. Their exact targets use only the standard
allowed axioms. The first group, `PackedNamespaced.Chunk036`, compiled in 198.63
seconds and passed HandoffAudit in 23.77 seconds in a disposable scratch source
workspace. Its transport and every source member were hash-checked. This
confirms a dependency group, not the full case1464 certificate.

The guarded live pool retains its ceiling of six single-threaded checks and
eight live group transports. Source copies use a separate scratch workspace;
the pinned compiler, supplied target checker and genuine receipt validation are
retained. A proposed extra manual test found the automatic checker already
running: it borrowed no slot, started no extra compiler, and was not a proof
failure. The original precheck metadata was preserved beside its correction.

Small portable tools are in [`scripts/t03_retry/`](scripts/t03_retry/README.md).
They include the depth planner, generalized producer, compiler-boundary queue
transition, scratch source worker and one-thread runtime defaults. Machine
paths are explicit arguments. Python source/help checks, a dependency-depth
fixture, and receipt mismatch negative controls passed. The portable copies
have not been replayed in Lean. The existing dispatcher must enforce the global
pool ceiling; these tools do not create a worker pool.

`verification/t03-case1464-parallel-retry.json` records the sanitized actual
audits, source bindings, transition and corrected manual precheck. The large
pending generated Lean closure and runtime logs/caches are excluded. Complete
published case source closures are now **156/173**, with **17 cases remaining**;
case1464, public target assembly, combined audits and the final return ZIP are
still pending. This checkpoint adds no new release asset or completed case.

## External returned-case handoff

External progress reports name fifteen finished cases, but the inspected public
branches do not supply their generated per-case source closures or matching
individual target audits. These reports add no accepted cases to this count.
Cases 1848 and 2047 are two of those fifteen and are now independently accepted
here, leaving thirteen possible additions once exact sources and audits are delivered.

[PR 2](https://github.com/Queuingtheorydotcom/11SquaresFormalized/pull/2) provides
the conditional per-case adapter
`ElevenSquare.Interop.Wand125.certificate_of_maskAt`. Each actual upstream
`CaseExcluded (maskAt k)` proof can use that adapter without waiting for a full
family theorem. The inspected integration checkpoint records selected-module
checks on Lean 4.34.1, while these source assets pin Lean 4.10.0-rc2; a complete
toolchain integration and target replay are not claimed.

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
closure is now supplied. The other 149 audited case source collections were
outside that original one-case Git checkpoint. Their complete exact source closures are now supplied
in the separately published release asset described above.

A measurement of those 150 completed-check source manifests found 98,369
distinct Lean source files, totaling 5,350,077,814 bytes before deduplication
against the repository. The common-helper snapshot already supplied 54 of those
files, leaving 98,315 files and 5,349,623,026 bytes to add for the entire snapshot.
No conflicting source versions were found. This was a manifest-only measurement;
the full collection was not extracted, rebuilt, or published at that stage.
It was subsequently published in the standalone 151-case release asset. The
one-case checkpoint keeps the added Git source manageable while supplying a complete proof
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
