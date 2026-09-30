import ElevenSquare.Pending.S08_GapDefinitions
import ElevenSquare.Pending.S08_SeparationGeometry
import Mathlib.Tactic.FinCases

namespace ElevenSquare.Pending
noncomputable section

/-- All four perturbed corners belong to the corresponding actual closed square. -/
theorem perturbedCorner_closed (q₀ : Owner → UnitSquare) (h : Displacement)
    (i : Owner) (q : UnitSquare)
    (hc : q.center = perturbedCenter q₀ h i)
    (ha : q.axis = perturbedAxis q₀ h i) (v : Fin 4) :
    ClosedSquare q (perturbedCorner q₀ h i v) := by
  have hs : |(cornerSigns v).1/2| ≤ (1:ℝ)/2 := by
    fin_cases v <;> norm_num [cornerSigns, abs_div]
  have ht : |(cornerSigns v).2/2| ≤ (1:ℝ)/2 := by
    fin_cases v <;> norm_num [cornerSigns, abs_div]
  have hp := SeparationGeometry.closed_affine_point q _ _ hs ht
  simpa only [perturbedCorner, hc, ha] using hp

#print axioms perturbedCorner_closed

end
end ElevenSquare.Pending
