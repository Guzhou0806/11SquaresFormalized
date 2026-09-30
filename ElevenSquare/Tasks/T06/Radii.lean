import ElevenSquare.Pending.S08_Packet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace ElevenSquare.Pending.T06
noncomputable section

def focusedMaxRadius : ℝ := 67647473 / 10000000000

theorem focusedRadii_bounds (j : Fin 33) :
    0 < focusedRadii j ∧ focusedRadii j ≤ focusedMaxRadius ∧
      focusedRadii j ≤ 1/64 := by
  fin_cases j <;> norm_num [focusedRadii, focusedMaxRadius]

theorem focusedMaxRadius_pos : 0 < focusedMaxRadius := by
  norm_num [focusedMaxRadius]

theorem focusedRadii_attains_max : focusedRadii 32 = focusedMaxRadius := by
  rfl

theorem focusedRectangle_in_small_box (h : Displacement)
    (hh : InRectangle focusedRadii h) : ∀ j, |h j| ≤ 1/64 := by
  intro j
  exact (hh j).trans (focusedRadii_bounds j).2.2

end
end ElevenSquare.Pending.T06
