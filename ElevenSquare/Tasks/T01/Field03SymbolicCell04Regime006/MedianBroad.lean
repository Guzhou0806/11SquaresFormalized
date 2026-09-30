import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.MedianBridge

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_majority_broad (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlo : ((1795/4096 : ℚ) : ℝ) ≤ t)
    (hhi : t ≤ ((2531/4096 : ℚ) : ℝ))
    (hcontains : SymbolicPolygonContains target00 t q.center) :
    BaselineMajorityCapture baselineField03Sites 2 q :=
  target00_majority q t hlo hhi ha hcontains

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.target00_majority_broad
