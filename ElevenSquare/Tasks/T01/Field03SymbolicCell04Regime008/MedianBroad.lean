import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.MedianBridge

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_majority_broad (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlo : ((633/1024 : ℚ) : ℝ) ≤ t)
    (hhi : t ≤ ((4095/4096 : ℚ) : ℝ))
    (hcontains : SymbolicPolygonContains target00 t q.center) :
    BaselineMajorityCapture baselineField03Sites 2 q :=
  target00_majority q t hlo hhi ha hcontains

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.target00_majority_broad
