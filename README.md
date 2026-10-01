# Eleven-square packing in Lean

This repository assembles the completed foundations and the available partial
formalizations of the optimal eleven-square packing. **Global optimality is
still unfinished.** Six explicit `sorry` sites record the remaining obligations.
A build that accepts those sites checks the surrounding code but does not prove
the final optimality theorem. See [MISSING.md](MISSING.md).

At the latest checkpoint, **157/173** full case source closures remain
published and 16 case certificates remain. The new equality repairs preserve
already issued source closures. Case1464 groups 203/209 have clean actual target
audits; case1731's repaired Chunk009 elaborates successfully. All four updated
case1464,1465,1372 and1731 source versions remain pending their full target audits.
The compact tools and exact source bindings are in [T03_PROGRESS.md](T03_PROGRESS.md).
Native source synchronization measured 3.734 seconds versus 11.665 seconds on
the same 381-member fixture, and has now run in an actual new proof job.

The returned-case common tools now include a proved center-distance collision
shortcut, an ordinary kernel-checked Boolean tactic, and the complete source
closure of the independently audited case2135 certificate. The supplied
checkpoint and the precise limits of the ongoing case progress are described in
[T03_PROGRESS.md](T03_PROGRESS.md). The public 173-case obligation remains open.

The common tools also include an independently tested equality-reflexivity
helper that reduced one eight-proof coordinate sample from 7.039 to 4.368
seconds. Its kernel negative control rejected a false equality; see the
progress document for the exact evidence and unfinished-case status.

A [partial T03 release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited-151-20260930) supplies the complete exact source
checkpoint for 151 independently audited cases, plus standalone supplements
for cases 1484, 2122, 1646, 2047, 1848, and 1311: **157 of 173** cases now have
published complete source closures. The public family assembly and its clean
combined target audits are still unfinished; 16 case certificates remain.

Case 1372's two isolated binding statements now pass the original Lean
checker with only `propext`; their exact source and audit are included. Its
full-case retry is queued and remains pending. Case 2069 has 13 of 120 accepted
dependency groups at the 04:54 UTC snapshot. These do not add completed cases;
see the progress document for the precise evidence and limits.

A separate [pending source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-pending-case-retries-20261001) supplies the immutable prepared
source closures for cases 1464, 1465, 2069 and 1372. All four full-case
audits remain pending at this checkpoint; these assets add no accepted cases.
Every source member is hash-bound to its original transport, with portable
serial metadata. The earlier 15 accepted release assets remain unchanged; the
new case1311 supplement adds its separately accepted source and metadata.

The latest case1372 retry preserves the checked first nine chunks and repairs
8,813 remaining generated equality proof constructions. Its full Chunk009
now elaborates successfully; the full certificate audit remains pending.
Genuine receipt sharing now includes both source-workspace locations and the
separate primary scratch donor, with object hashes checked before copying.

The target side length is the exact real number

\[
T = \frac{6u+4}{1+2u-u^2},
\]

where `u` is the unique root in `(9/25,37/100)` of

\[
5u^8-10u^7-2u^6+14u^5+12u^4-6u^3+2u^2+2u-1=0.
\]

The construction attains approximately `3.8770835900228141773`. The model allows
arbitrary orientations, legal boundary contact, and disjoint open interiors.

## Entry points

| File | Purpose |
| --- | --- |
| `ElevenSquare/Foundations.lean` | Geometry, the exact endpoint, attaining construction, closed-cell cover, and finite case reduction. |
| `ElevenSquare/Progress.lean` | Completed baseline groups, case1000 through two steps, and selected global capture helpers. |
| `ElevenSquare/Pending/` | Public interfaces and the later proof stages, with explicit remaining dependencies. |
| `ElevenSquare/Tasks/` | Returned certificate data, generic checkers, analytic lemmas, and concrete partial proofs. |
| `ElevenSquare/Optimality.lean` | Final unconditional theorem statements; their proofs currently inherit the listed admissions. |
| `ElevenSquare/Verification.lean` | Axiom queries for completed milestones and unfinished public targets. |

## Verification

Install Git and Lean's `elan` launcher. The project pins Lean `v4.10.0-rc2` and
mathlib revision `3fef63ff3bda38478ba4364ff03999f0246745a2`.
Keep `lake-manifest.json`; do not update dependencies while reproducing this
snapshot.

Set up the public dependencies, compile the main dependency chain serially,
and inspect its target axioms with one command:

```sh
python3 scripts/verify.py --setup
```

For every included source module, including progress outside the main chain:

```sh
python3 scripts/verify.py --setup --all
```

Once dependencies are installed, omit `--setup`. Accepted unchanged modules
can be resumed using the script's source/object/dependency fingerprints. Add
`--fresh` to rebuild every selected local module. These are substantial exact
certificate checks and can take a long time. They use ordinary Lean checking;
no packing search or external algebra system is required.

A source-only check, requiring only Python3, is:

```sh
python3 scripts/check_sources.py
```

`--plan` on the verifier prints the compilation order without running Lean.
Build logs and objects remain in ignored `.verification/` and `.lake/` folders.
The normal Lake entry point is also available via `lake build`.

The verifier distinguishes clean milestones, which may use only `propext`,
`Classical.choice`, and `Quot.sound`, from the explicit unfinished targets.
Success with the current six admissions is **partial assembly success**, not a
proof of optimality. Closing those admissions requires a fresh final audit.

## Assembly provenance

The source incorporates the baseline partial return, the checked prior-support
continuation, the local-packet return, and the global partial handoff. It also
preserves the previously integrated fixes to the overlay and D4 bridge from the
earlier current-work return. Older unreferenced speculative modules are omitted;
all delivered Lean modules and their local source dependencies are preserved.

`verification/source-inventory.json` records exact source hashes and which files
match supplied compiler inventories. `verification/imported-audits.json` retains
only mathematical declaration names and their reported axiom sets. It is
historical evidence, not a fresh combined compiler replay. In particular, a
reported inherited admission may have been removed by another merged return.

The assembly was checked for a complete local import closure, exact admission
inventory, matching returned source hashes, and personal information. The small
final composition is checked separately against the existing shared interfaces.
The entire large numerical certificate collection is supplied for reproducible
replay rather than claimed freshly rebuilt during packaging.

Only portable source, pinned public dependency metadata, mathematical audit
summaries, and fresh documentation are distributed. Original handoff archives,
conversation records, machine diagnostics, private project identifiers, and
historical machine-specific logs are omitted.
