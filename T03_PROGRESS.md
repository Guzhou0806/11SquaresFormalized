# Returned-case common tools: partial progress

The returned family still requires certificates for all 173 assigned indices.
`ElevenSquare.Pending.returned_certificate_exists` remains admitted in this
repository, and global optimality remains unfinished. This update adds checked
common proof tools; it does not discharge that public obligation.

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

## Audit scope

The six distance/collision declarations passed an independent compiler audit
with only `propext`, `Classical.choice`, and `Quot.sound`. The tactic was checked
with the same pinned Lean 4.10.0-rc2 toolchain and mathlib revision as this
repository. `verification/t03-progress.json` records portable declaration names,
axiom sets, and source hashes. These are reported independent checks, not a
fresh replay of the entire merged assembly.

Separate ongoing work had completed full audits for 150 of the 173 case
certificates at this snapshot. The large generated case source collection is
not included in this compact update. Its declaration list in the progress
record is informational and supplies no certificate proof here. The remaining
23 cases, assembly of both exact public returned targets, their clean axiom
audit, and the completed return package remain unfinished.

To reproduce the included source and main audit serially in a full checkout:

```sh
python3 scripts/check_sources.py
python3 scripts/verify.py --setup
```

`--all` on the verifier checks every included module. Acceptance of the six
existing admissions still means partial assembly success; see [MISSING.md](MISSING.md).
