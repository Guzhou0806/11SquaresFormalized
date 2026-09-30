import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCover
import ElevenSquare.Tasks.T01.SymbolicWall

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Multiplying a constant normal by the chart denominator `1+t²`. -/
def SymbolicQuadratic.scaleByChart (r : ℚ) : SymbolicQuadratic :=
  ⟨r, 0, r⟩

/-- Clear the positive chart denominator from a wall or cell facet. -/
def scaledWallFacet (f : SymbolicWallFacet) : SymbolicFacet :=
  ⟨SymbolicQuadratic.scaleByChart f.a,
   SymbolicQuadratic.scaleByChart f.b,
   ⟨f.c + f.d / 2, f.d, f.c - f.d / 2⟩⟩

theorem scaled_wall_normal_eval (r : ℚ) (t : ℝ) :
    (SymbolicQuadratic.scaleByChart r).eval t = (1+t^2) * r := by
  unfold SymbolicQuadratic.scaleByChart SymbolicQuadratic.eval
  push_cast
  ring

theorem scaled_wall_bound_eval (f : SymbolicWallFacet) (t : ℝ) :
    (scaledWallFacet f).c.eval t =
      (1+t^2) * ((f.c : ℝ) + f.d * exactWallMargin t) := by
  have hd : 0 < 1+t^2 := by positivity
  have hmargin : (1+t^2) * exactWallMargin t =
      (1-t^2+2*t)/2 := by
    rw [exactWallMargin_formula]
    field_simp [ne_of_gt hd]
    ring
  change ((f.c + f.d / 2 : ℚ) : ℝ) + (f.d:ℝ)*t +
      ((f.c - f.d / 2 : ℚ) : ℝ)*t^2 =
        (1+t^2) * ((f.c:ℝ) + f.d * exactWallMargin t)
  calc
    _ = (1+t^2)*(f.c:ℝ) + (f.d:ℝ)*((1-t^2+2*t)/2) := by
      push_cast
      ring
    _ = (1+t^2)*(f.c:ℝ) + (f.d:ℝ)*((1+t^2)*exactWallMargin t) := by rw [hmargin]
    _ = (1+t^2) * ((f.c:ℝ) + f.d * exactWallMargin t) := by
      ring

theorem symbolic_wall_scaled_contains (f : SymbolicWallFacet) (t : ℝ)
    (p : Point) (hf : f.contains t p) : (scaledWallFacet f).contains t p := by
  have hd : 0 ≤ 1+t^2 := by positivity
  change (SymbolicQuadratic.scaleByChart f.a).eval t * p.1 +
      (SymbolicQuadratic.scaleByChart f.b).eval t * p.2 ≤
        (scaledWallFacet f).c.eval t
  rw [scaled_wall_normal_eval, scaled_wall_normal_eval,
    scaled_wall_bound_eval]
  calc
    (1+t^2) * (f.a:ℝ) * p.1 + (1+t^2) * (f.b:ℝ) * p.2 =
        (1+t^2) * ((f.a:ℝ)*p.1 + (f.b:ℝ)*p.2) := by ring
    _ ≤ (1+t^2) * ((f.c:ℝ) + f.d * exactWallMargin t) := by
      exact mul_le_mul_of_nonneg_left hf hd

/-- The 24 source facets used by a symbolic field row. The first four are
exact moving wall bounds; the remaining twenty are the cell bounds in their
existing `baselineCellPolygon` order. -/
def symbolicWallScaledSlab (cell : Fin 16) : List SymbolicFacet :=
  (symbolicWallSlab cell).map scaledWallFacet

theorem symbolic_wall_scaled_slab_contains (q : UnitSquare)
    (cell : Fin 16) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell cell (normalizeCenter q.center)) :
    SymbolicPolygonContains (symbolicWallScaledSlab cell) t q.center := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact symbolic_wall_scaled_contains g t q.center
    (symbolic_wall_slab_contains q cell t ha hcont hcell g hg)

/-- A checked moving BSP applies to every actual square in the named cell
throughout its rational chart interval. -/
theorem symbolic_wall_cover_for_square (q : UnitSquare)
    (cell : Fin 16) (t : ℝ) (l u : ℚ)
    (targets : List (List SymbolicFacet)) (cert : SymbolicCoverCertificate)
    (hc : cert.Check (symbolicWallScaledSlab cell) targets l u)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell cell (normalizeCenter q.center)) :
    ∃ target ∈ targets, SymbolicPolygonContains target t q.center := by
  exact symbolic_cover_sound (symbolicWallScaledSlab cell) targets l u cert hc
    t hlt htu q.center
    (symbolic_wall_scaled_slab_contains q cell t ha hcont hcell)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_wall_scaled_slab_contains
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_wall_cover_for_square
