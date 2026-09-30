import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianAxisOrder
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo

namespace ElevenSquare.Tasks.T01.Field03SymbolicMedian
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
noncomputable section

theorem u20_A_check :
    (axisUOrderPoly site2 site0).BernsteinNonnegCheck (1/4096) (309/2048) := by
  norm_num [axisUOrderPoly, site2, site0, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem u01_A_check :
    (axisUOrderPoly site0 site1).BernsteinNonnegCheck (1/4096) (309/2048) := by
  norm_num [axisUOrderPoly, site0, site1, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem u20_A (t : ℝ)
    (hlo : ((1/4096:ℚ):ℝ) ≤ t) (hhi : t ≤ ((309/2048:ℚ):ℝ)) :
    dot (chartNumeratorNormal t (1, 0)) (realPoint site2) ≤
      dot (chartNumeratorNormal t (1, 0)) (realPoint site0) :=
  axis_u_order_of_bernstein site2 site0 (1/4096) (309/2048)
    u20_A_check t hlo hhi

theorem u01_A (t : ℝ)
    (hlo : ((1/4096:ℚ):ℝ) ≤ t) (hhi : t ≤ ((309/2048:ℚ):ℝ)) :
    dot (chartNumeratorNormal t (1, 0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (1, 0)) (realPoint site1) :=
  axis_u_order_of_bernstein site0 site1 (1/4096) (309/2048)
    u01_A_check t hlo hhi

end
end ElevenSquare.Tasks.T01.Field03SymbolicMedian

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicMedian.u20_A
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicMedian.u01_A
