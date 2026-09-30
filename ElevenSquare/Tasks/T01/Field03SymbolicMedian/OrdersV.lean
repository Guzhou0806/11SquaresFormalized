import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianAxisOrder
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo

namespace ElevenSquare.Tasks.T01.Field03SymbolicMedian
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
noncomputable section

theorem v10_check :
    (axisVOrderPoly site1 site0).BernsteinNonnegCheck 0 1 := by
  norm_num [axisVOrderPoly, site0, site1, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem v02_check :
    (axisVOrderPoly site0 site2).BernsteinNonnegCheck 0 1 := by
  norm_num [axisVOrderPoly, site0, site2, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem v10_order (t : ℝ) (hlo : 0 ≤ t) (hhi : t ≤ 1) :
    dot (chartNumeratorNormal t (0, 1)) (realPoint site1) ≤
      dot (chartNumeratorNormal t (0, 1)) (realPoint site0) := by
  apply axis_v_order_of_bernstein site1 site0 0 1 v10_check t
  · simpa using hlo
  · simpa using hhi

theorem v02_order (t : ℝ) (hlo : 0 ≤ t) (hhi : t ≤ 1) :
    dot (chartNumeratorNormal t (0, 1)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (0, 1)) (realPoint site2) := by
  apply axis_v_order_of_bernstein site0 site2 0 1 v02_check t
  · simpa using hlo
  · simpa using hhi

end
end ElevenSquare.Tasks.T01.Field03SymbolicMedian

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicMedian.v10_order
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicMedian.v02_order
