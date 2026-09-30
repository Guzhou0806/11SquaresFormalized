import ElevenSquare.Pending.S08_SATCoordinates

namespace ElevenSquare.Pending.SATRadii
noncomputable section
open SATCoordinates

def threshold (a b : UnitSquare) : ℝ := 1 + |cosine a b| + |sine a b|

theorem radius_a (a b : UnitSquare) :
    projectionRadius a a.axis + projectionRadius b a.axis = threshold a b / 2 := by
  rw [projectionRadius_axis]
  have hc : dot b.axis a.axis = cosine a b := dot_comm _ _
  have hs : dot (perp b.axis) a.axis = -sine a b := by
    rw [dot_comm]; exact cross_perp a b
  simp only [projectionRadius, hc, hs, abs_neg, threshold]
  ring

theorem radius_perp_a (a b : UnitSquare) :
    projectionRadius a (perp a.axis) + projectionRadius b (perp a.axis) = threshold a b / 2 := by
  rw [projectionRadius_perp_axis]
  have hs : dot b.axis (perp a.axis) = sine a b := dot_comm _ _
  have hc : dot (perp b.axis) (perp a.axis) = cosine a b := by
    rw [dot_comm]; exact both_perp a b
  simp only [projectionRadius, hc, hs, threshold]
  ring

theorem radius_b (a b : UnitSquare) :
    projectionRadius a b.axis + projectionRadius b b.axis = threshold a b / 2 := by
  rw [projectionRadius_axis]
  change (|cosine a b| + |sine a b|)/2 + 1/2 = threshold a b / 2
  unfold threshold
  ring

theorem radius_perp_b (a b : UnitSquare) :
    projectionRadius a (perp b.axis) + projectionRadius b (perp b.axis) = threshold a b / 2 := by
  rw [projectionRadius_perp_axis]
  simp only [projectionRadius, cross_perp, both_perp, abs_neg, threshold]
  ring

theorem radius_four (a b : UnitSquare) (v : Point)
    (hv : v ∈ ([a.axis, perp a.axis, b.axis, perp b.axis] : List Point)) :
    projectionRadius a v + projectionRadius b v = threshold a b / 2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact radius_a a b
  · exact radius_perp_a a b
  · exact radius_b a b
  · exact radius_perp_b a b

#print axioms radius_a
#print axioms radius_perp_a
#print axioms radius_b
#print axioms radius_perp_b
#print axioms radius_four
end
end ElevenSquare.Pending.SATRadii
