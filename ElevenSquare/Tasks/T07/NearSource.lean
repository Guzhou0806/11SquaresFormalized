import ElevenSquare.Tasks.T07.NearHull

/-! Exact rational final pose domains for the near case-438 leaf. Each generated
`NearSourceData*` file contains the full closed half-angle intervals and the
residual polygons for one construction role. The finite Lean checks use `decide`
and never defer the rational inequalities to the external receipt. -/
namespace ElevenSquare.Tasks.T07

structure NearRatRect where
  lx : ℚ
  hx : ℚ
  ly : ℚ
  hy : ℚ

def NearRatRect.Contains (b : NearRatRect) (p : ℚ × ℚ) : Prop :=
  b.lx ≤ p.1 ∧ p.1 ≤ b.hx ∧ b.ly ≤ p.2 ∧ p.2 ≤ b.hy

structure NearPoseRow where
  lo : ℚ
  hi : ℚ
  polygons : List (List (ℚ × ℚ))

def NearPoseRow.Valid (b : NearRatRect) (axis : Bool) (r : NearPoseRow) : Prop :=
  0 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ 1 ∧
    (if axis then r.hi ≤ Rat.divInt 1 2 ∨ Rat.divInt 1 2 ≤ r.lo
      else r.hi < Rat.divInt 2 3) ∧
    List.Forall (fun P => P ≠ [] ∧ List.Forall b.Contains P) r.polygons

end ElevenSquare.Tasks.T07
