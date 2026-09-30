import ElevenSquare.Tasks.T01.SymbolicWallCover

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- The projection difference between a target point and an anchor point. -/
def wallProjectionDifference (k : Fin 4) (anchor p : QPoint) : WallQuadratic :=
  (wallDirectionPolynomials k).1.linear (wallDirectionPolynomials k).2
    (p.1 - anchor.1) (p.2 - anchor.2)

def WallProjectionCheck (k : Fin 4) (anchor p : QPoint) (l u : ℚ) : Prop :=
  (wallProjectionDifference k anchor p).quartic.BernsteinNonnegCheck l u

theorem wall_projection_difference_eval (k : Fin 4) (anchor p : QPoint) (t : ℝ) :
    (wallProjectionDifference k anchor p).eval t =
      dot (chartDirectionNumerator t k) (realPoint p) -
      dot (chartDirectionNumerator t k) (realPoint anchor) := by
  fin_cases k <;>
    simp [wallProjectionDifference, chartDirectionNumerator, wallDirectionPolynomials,
      WallQuadratic.linear, WallQuadratic.eval, dot, realPoint] <;>
    push_cast <;> ring

theorem wall_projection_check_sound (k : Fin 4) (anchor p : QPoint) (l u : ℚ)
    (hc : WallProjectionCheck k anchor p l u) (t : ℝ)
    (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) :
    dot (chartDirectionNumerator t k) (realPoint anchor) ≤
      dot (chartDirectionNumerator t k) (realPoint p) := by
  have hp := wall_quadratic_bernstein_nonneg _ l u hc t hl hu
  rw [wall_projection_difference_eval] at hp
  linarith only [hp]

theorem wall_dual_supports_of_projection (f g : SymbolicWallFacet) (k : Fin 4)
    (anchor p : QPoint) (t : ℝ) (hs : WallDualSupports f g k anchor t)
    (hd : dot (chartDirectionNumerator t k) (realPoint anchor) ≤
      dot (chartDirectionNumerator t k) (realPoint p)) :
    WallDualSupports f g k p t := by
  obtain ⟨a, b, ha, hb, hx, hy, hm⟩ := hs
  exact ⟨a, b, ha, hb, hx, hy, by linarith only [hm, hd]⟩

/-- A regime checks expensive wall margins only at its anchor points. Every
other point has a certified no-smaller projection than an anchor. -/
inductive AnchoredWallDirectionCertificate where
  | ordinary (f g : SymbolicWallFacet) (anchors : List QPoint)
  | crossing (f g h : SymbolicWallFacet) (ratio : ℚ) (anchors : List QPoint)
  | split (mid : ℚ) (left right : AnchoredWallDirectionCertificate)

def AnchoredWallDirectionCertificate.Check (cert : AnchoredWallDirectionCertificate)
    (cell : Fin 16) (k : Fin 4) (points : List QPoint) (l u : ℚ) : Prop :=
  match cert with
  | .ordinary f g anchors =>
      f ∈ symbolicWallSlab cell ∧ g ∈ symbolicWallSlab cell ∧
        (∀ a ∈ anchors, WallDualCheck f g k a l u) ∧
        (∀ p ∈ points, ∃ a ∈ anchors, WallProjectionCheck k a p l u)
  | .crossing f g h r anchors =>
      f ∈ symbolicWallSlab cell ∧ g ∈ symbolicWallSlab cell ∧
        h ∈ symbolicWallSlab cell ∧
        (∀ a ∈ anchors, WallDualCrossingCheck f g h k a l u r) ∧
        (∀ p ∈ points, ∃ a ∈ anchors, WallProjectionCheck k a p l u)
  | .split mid left right =>
      l ≤ mid ∧ mid ≤ u ∧ left.Check cell k points l mid ∧ right.Check cell k points mid u

theorem anchored_wall_direction_certificate_sound
    (cert : AnchoredWallDirectionCertificate) (cell : Fin 16) (k : Fin 4)
    (points : List QPoint) (l u : ℚ) (hc : cert.Check cell k points l u)
    (p : QPoint) (hp : p ∈ points) (t : ℝ)
    (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) :
    ∃ f ∈ symbolicWallSlab cell, ∃ g ∈ symbolicWallSlab cell,
      WallDualSupports f g k p t := by
  induction cert generalizing l u with
  | ordinary f g anchors =>
    obtain ⟨a, ha, hd⟩ := hc.2.2.2 p hp
    have hs := wall_dual_check_sound f g k a l u (hc.2.2.1 a ha) t hl hu
    exact ⟨f, hc.1, g, hc.2.1,
      wall_dual_supports_of_projection f g k a p t hs
        (wall_projection_check_sound k a p l u hd t hl hu)⟩
  | crossing f g h r anchors =>
    obtain ⟨a, ha, hd⟩ := hc.2.2.2.2 p hp
    have hproj := wall_projection_check_sound k a p l u hd t hl hu
    rcases wall_dual_crossing_check_sound f g h k a l u r
      (hc.2.2.2.1 a ha) t hl hu with hs | hs
    · exact ⟨f, hc.1, g, hc.2.1,
        wall_dual_supports_of_projection f g k a p t hs hproj⟩
    · exact ⟨g, hc.2.1, h, hc.2.2.1,
        wall_dual_supports_of_projection g h k a p t hs hproj⟩
  | split mid left right ihl ihr =>
    by_cases hm : t ≤ (mid : ℝ)
    · exact ihl l mid hc.2.2.1 hl hm
    · exact ihr mid u hc.2.2.2 (le_of_not_ge hm) hu

theorem anchored_symbolic_wall_owned_points
    (certs : Fin 4 → AnchoredWallDirectionCertificate)
    (cell : Fin 16) (points : List QPoint)
    (hc : ∀ k, (certs k).Check cell k points 0 1)
    (q : UnitSquare) (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ points, OpenSquare q (realPoint p) := by
  obtain ⟨t, ht0, ht1, ha⟩ := hchart
  intro p hp
  apply symbolic_wall_point_owned q cell (realPoint p) t ha hcont hcell
  intro k
  obtain ⟨f, hf, g, hg, hw⟩ :=
    anchored_wall_direction_certificate_sound (certs k) cell k points 0 1
      (hc k) p hp t (by simpa using ht0) (by simpa using ht1)
  exact ⟨f, hf, g, hg, hw⟩

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.anchored_symbolic_wall_owned_points
