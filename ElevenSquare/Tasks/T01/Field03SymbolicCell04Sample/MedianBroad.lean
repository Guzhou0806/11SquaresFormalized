import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.MedianBridge
import ElevenSquare.Tasks.T01.Field03SymbolicMedian.OrdersA
import ElevenSquare.Tasks.T01.Field03SymbolicMedian.OrdersV

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem target00_majority_broad (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlo : ((1/4096 : ℚ) : ℝ) ≤ t)
    (hhi : t ≤ ((309/2048 : ℚ) : ℝ))
    (hcontains : SymbolicPolygonContains target00 t q.center) :
    BaselineMajorityCapture baselineField03Sites 2 q := by
  have ht0 : 0 ≤ t := by
    norm_num at hlo
    linarith
  have ht1 : t ≤ 1 := by
    norm_num at hhi
    linarith
  exact target00_majority_of_orders q t
    (Field03SymbolicMedian.u01_A t hlo hhi)
    (Field03SymbolicMedian.u20_A t hlo hhi)
    (Field03SymbolicMedian.v02_order t ht0 ht1)
    (Field03SymbolicMedian.v10_order t ht0 ht1)
    ha hcontains

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_majority_broad
