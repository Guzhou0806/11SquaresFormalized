import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime008.Data
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime008
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_eq_representative :
    target00 = Field03SymbolicCell04Regime006.target00 := by
  rfl

theorem interval_in_representative (t : ℝ)
    (hlo : ((1795/4096:ℚ):ℝ) ≤ t)
    (hhi : t ≤ ((1001/2048:ℚ):ℝ)) :
    ((1795/4096:ℚ):ℝ) ≤ t ∧ t ≤ ((2531/4096:ℚ):ℝ) := by
  constructor
  · exact le_trans (by norm_num) hlo
  · exact le_trans hhi (by norm_num)

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime008

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime008.target00_eq_representative
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime008.interval_in_representative
