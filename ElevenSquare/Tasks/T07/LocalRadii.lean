import ElevenSquare.Pending.S08_Packet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact elementary facts about the coordinatewise local rectangle. -/

namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def focusedMaxRadius : ℝ := 67647473 / 10000000000

theorem focusedRadii_bounds (j : Fin 33) :
    0 < focusedRadii j ∧ focusedRadii j ≤ focusedMaxRadius ∧
      focusedRadii j ≤ 1 / 64 := by
  fin_cases j <;> norm_num [focusedRadii, focusedMaxRadius]

theorem focusedMaxRadius_attained :
    focusedRadii ⟨32, by omega⟩ = focusedMaxRadius := by
  norm_num [focusedRadii, focusedMaxRadius]

/-- The tenth angular coordinate requires the focused rectangle: its radius
exceeds the older uniform `1/248` neighborhood. -/
theorem focused_tenth_angle_exceeds_uniform :
    1 / 248 < focusedRadii (coordinate 10 2) := by
  have hc : coordinate (10 : Owner) (2 : Fin 3) = (32 : Fin 33) := by decide
  rw [hc]
  change 1 / 248 < focusedRadii ⟨32, by omega⟩
  rw [focusedMaxRadius_attained]
  norm_num [focusedMaxRadius]

end
end ElevenSquare.Tasks.T07
