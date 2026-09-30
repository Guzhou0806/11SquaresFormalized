import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.Data
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_eq_representative :
    target00 = Field03SymbolicCell04Regime008.target00 := by
  rfl

theorem interval_in_representative (t : ℝ)
    (hlo : ((1923/2048:ℚ):ℝ) ≤ t)
    (hhi : t ≤ ((4069/4096:ℚ):ℝ)) :
    ((633/1024:ℚ):ℝ) ≤ t ∧ t ≤ ((4095/4096:ℚ):ℝ) := by
  constructor
  · exact le_trans (by norm_num) hlo
  · exact le_trans hhi (by norm_num)

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.target00_eq_representative
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.interval_in_representative
