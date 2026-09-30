import ElevenSquare.Pending.S08_GapCorners

namespace ElevenSquare.Pending
noncomputable section

theorem feasible_wall_gaps (S : ℝ) (q₀ : Owner → UnitSquare) (h : Displacement)
    (hf : LocalFeasible S q₀ h) (i : Owner) (v w : Fin 4) :
    0 ≤ gapValue S q₀ (.wall i v w) h  := by
  obtain ⟨P, hP⟩ := hf
  have hc := perturbedCorner_closed q₀ h i (P.squares i) (hP i).1 (hP i).2 v
  have hp := P.contained i (perturbedCorner q₀ h i v) hc
  rcases hp with ⟨hx0, hxS, hy0, hyS⟩
  fin_cases w
  · exact hx0
  · exact sub_nonneg.mpr hxS
  · exact hy0
  · exact sub_nonneg.mpr hyS

#print axioms feasible_wall_gaps

end
end ElevenSquare.Pending
