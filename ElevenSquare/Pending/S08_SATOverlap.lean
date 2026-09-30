import ElevenSquare.Pending.S08_SATRadii
import ElevenSquare.Pending.S08_SATSigned

namespace ElevenSquare.Pending.SATOverlap
noncomputable section
open SATCoordinates SATRadii

/-- The scalar witness is a point of both actual open unit squares. -/
theorem actual_overlap (a b : UnitSquare)
    (hX : |2*dot (b.center-a.center) a.axis| < threshold a b)
    (hY : |2*dot (b.center-a.center) (perp a.axis)| < threshold a b)
    (hU : |2*dot (b.center-a.center) b.axis| < threshold a b)
    (hV : |2*dot (b.center-a.center) (perp b.axis)| < threshold a b) :
    ∃ p : Point, OpenSquare a p ∧ OpenSquare b p := by
  have hUR : 2*dot (b.center-a.center) b.axis =
      cosine a b * (2*dot (b.center-a.center) a.axis) +
      sine a b * (2*dot (b.center-a.center) (perp a.axis)) := by
    rw [vector_basis a (b.center-a.center) b.axis]
    dsimp [cosine, sine]
    ring
  have hVR : 2*dot (b.center-a.center) (perp b.axis) =
      -sine a b * (2*dot (b.center-a.center) a.axis) +
      cosine a b * (2*dot (b.center-a.center) (perp a.axis)) := by
    rw [vector_basis a (b.center-a.center) (perp b.axis), cross_perp, both_perp]
    ring
  obtain ⟨x, y, hx, hy, hcx, hcy⟩ := SATSigned.overlap (cosine a b) (sine a b)
    (2*dot (b.center-a.center) a.axis) (2*dot (b.center-a.center) (perp a.axis))
    (2*dot (b.center-a.center) b.axis) (2*dot (b.center-a.center) (perp b.axis))
    (relative_unit a b) hUR hVR hX hY hU hV
  let p : Point := a.center + (x/2) • a.axis + (y/2) • perp a.axis
  have ha₁ : localX a p = x/2 := localX_affine a _ _
  have ha₂ : localY a p = y/2 := localY_affine a _ _
  have hb₁ : localX b p =
      (cosine a b*x+sine a b*y-2*dot (b.center-a.center) b.axis)/2 := by
    rw [localX_change a b p, ha₁, ha₂]
    ring
  have hb₂ : localY b p =
      (-sine a b*x+cosine a b*y-2*dot (b.center-a.center) (perp b.axis))/2 := by
    rw [localY_change a b p, ha₁, ha₂]
    ring
  refine ⟨p, ?_, ?_⟩
  · exact ⟨by rw [ha₁]; exact half_abs_lt hx, by rw [ha₂]; exact half_abs_lt hy⟩
  · exact ⟨by rw [hb₁]; exact half_abs_lt hcx, by rw [hb₂]; exact half_abs_lt hcy⟩

#print axioms actual_overlap
end
end ElevenSquare.Pending.SATOverlap
