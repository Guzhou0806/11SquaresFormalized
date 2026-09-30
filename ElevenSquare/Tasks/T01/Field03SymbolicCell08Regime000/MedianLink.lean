import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.Data
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_eq_representative :
    target00 = Field03SymbolicCell04Sample.target00 := by
  rfl

theorem interval_in_representative (t : ℝ)
    (hlo : ((1/4096:ℚ):ℝ) ≤ t)
    (hhi : t ≤ ((5/128:ℚ):ℝ)) :
    ((1/4096:ℚ):ℝ) ≤ t ∧ t ≤ ((309/2048:ℚ):ℝ) := by
  constructor
  · exact le_trans (by norm_num) hlo
  · exact le_trans hhi (by norm_num)

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.target00_eq_representative
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.interval_in_representative
