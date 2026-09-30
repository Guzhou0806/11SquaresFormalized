import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007.Data
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_eq_representative :
    target00 = Field03SymbolicCell04Regime006.target00 := by
  rfl

theorem interval_in_representative (t : ℝ)
    (hlo : ((65/128:ℚ):ℝ) ≤ t)
    (hhi : t ≤ ((2531/4096:ℚ):ℝ)) :
    ((1795/4096:ℚ):ℝ) ≤ t ∧ t ≤ ((2531/4096:ℚ):ℝ) := by
  constructor
  · exact le_trans (by norm_num) hlo
  · exact le_trans hhi (by norm_num)

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007.target00_eq_representative
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007.interval_in_representative
