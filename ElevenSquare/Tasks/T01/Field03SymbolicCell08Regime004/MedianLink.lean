import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.Data
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_eq_representative :
    target00 = Field03SymbolicCell04Regime002.target00 := by
  rfl

theorem interval_in_representative (t : ℝ)
    (hlo : ((203/1024:ℚ):ℝ) ≤ t)
    (hhi : t ≤ ((679/2048:ℚ):ℝ)) :
    ((619/4096:ℚ):ℝ) ≤ t ∧ t ≤ ((897/2048:ℚ):ℝ) := by
  constructor
  · exact le_trans (by norm_num) hlo
  · exact le_trans hhi (by norm_num)

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.target00_eq_representative
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.interval_in_representative
