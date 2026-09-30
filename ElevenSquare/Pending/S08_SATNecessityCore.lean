import ElevenSquare.Pending.S08_SATOverlap

namespace ElevenSquare.Pending.SATNecessity
noncomputable section
open SATRadii

/-- Necessity of the separating-axis criterion for arbitrary independently
rotated unit squares, with boundary contact allowed. -/
theorem necessary (a b : UnitSquare)
    (hdisjoint : ∀ p, ¬ (OpenSquare a p ∧ OpenSquare b p)) :
    ∃ v ∈ ([a.axis, -a.axis, perp a.axis, -(perp a.axis),
      b.axis, -b.axis, perp b.axis, -(perp b.axis)] : List Point),
      projectionRadius a v + projectionRadius b v ≤ dot (b.center-a.center) v := by
  by_contra hn
  have hlt (v : Point)
      (hv : v ∈ ([a.axis, -a.axis, perp a.axis, -(perp a.axis),
        b.axis, -b.axis, perp b.axis, -(perp b.axis)] : List Point)) :
      dot (b.center-a.center) v < projectionRadius a v + projectionRadius b v := by
    exact lt_of_not_ge (fun h => hn ⟨v, hv, h⟩)
  have hbound (v : Point)
      (hv : v ∈ ([a.axis, perp a.axis, b.axis, perp b.axis] : List Point)) :
      |2*dot (b.center-a.center) v| < threshold a b := by
    have hvpos : v ∈ ([a.axis, -a.axis, perp a.axis, -(perp a.axis),
        b.axis, -b.axis, perp b.axis, -(perp b.axis)] : List Point) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
      rcases hv with rfl | rfl | rfl | rfl <;> simp only [eq_self_iff_true, true_or, or_true]
    have hvneg : -v ∈ ([a.axis, -a.axis, perp a.axis, -(perp a.axis),
        b.axis, -b.axis, perp b.axis, -(perp b.axis)] : List Point) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
      rcases hv with rfl | rfl | rfl | rfl <;> simp only [eq_self_iff_true, true_or, or_true]
    have hp := hlt v hvpos
    have hm := hlt (-v) hvneg
    rw [SeparationGeometry.dot_neg_right, SeparationGeometry.radius_neg,
      SeparationGeometry.radius_neg] at hm
    rw [radius_four a b v hv] at hp hm
    apply abs_lt.mpr
    constructor <;> linarith only [hp, hm]
  obtain ⟨p, ha, hb⟩ := SATOverlap.actual_overlap a b
    (hbound a.axis (by simp only [List.mem_cons, List.not_mem_nil, or_false, eq_self_iff_true, true_or, or_true])) (hbound (perp a.axis) (by simp only [List.mem_cons, List.not_mem_nil, or_false, eq_self_iff_true, true_or, or_true]))
    (hbound b.axis (by simp only [List.mem_cons, List.not_mem_nil, or_false, eq_self_iff_true, true_or, or_true])) (hbound (perp b.axis) (by simp only [List.mem_cons, List.not_mem_nil, or_false, eq_self_iff_true, true_or, or_true]))
  exact hdisjoint p ⟨ha, hb⟩

#print axioms necessary
end
end ElevenSquare.Pending.SATNecessity
