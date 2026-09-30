import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianWorldBridge

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The cleared difference of two projections on the first chart axis. -/
def axisUOrderPoly (a b : QPoint) : Quartic :=
  ⟨b.1 - a.1, 2 * (b.2 - a.2), a.1 - b.1, 0, 0⟩

/-- The cleared difference of two projections on the second chart axis. -/
def axisVOrderPoly (a b : QPoint) : Quartic :=
  ⟨b.2 - a.2, -2 * (b.1 - a.1), a.2 - b.2, 0, 0⟩

theorem axis_u_order_poly_eval (a b : QPoint) (t : ℝ) :
    (axisUOrderPoly a b).eval t =
      dot (chartNumeratorNormal t (1, 0)) (realPoint b) -
        dot (chartNumeratorNormal t (1, 0)) (realPoint a) := by
  dsimp [axisUOrderPoly, Quartic.eval, chartNumeratorNormal, dot, realPoint]
  push_cast
  ring

theorem axis_v_order_poly_eval (a b : QPoint) (t : ℝ) :
    (axisVOrderPoly a b).eval t =
      dot (chartNumeratorNormal t (0, 1)) (realPoint b) -
        dot (chartNumeratorNormal t (0, 1)) (realPoint a) := by
  dsimp [axisVOrderPoly, Quartic.eval, chartNumeratorNormal, dot, realPoint]
  push_cast
  ring

theorem axis_u_order_of_bernstein (a b : QPoint) (l u : ℚ)
    (hc : (axisUOrderPoly a b).BernsteinNonnegCheck l u)
    (t : ℝ) (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ)) :
    dot (chartNumeratorNormal t (1, 0)) (realPoint a) ≤
      dot (chartNumeratorNormal t (1, 0)) (realPoint b) := by
  have hp := quartic_bernstein_nonneg (axisUOrderPoly a b) l u hc t hlt htu
  rw [axis_u_order_poly_eval] at hp
  linarith

theorem axis_v_order_of_bernstein (a b : QPoint) (l u : ℚ)
    (hc : (axisVOrderPoly a b).BernsteinNonnegCheck l u)
    (t : ℝ) (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ)) :
    dot (chartNumeratorNormal t (0, 1)) (realPoint a) ≤
      dot (chartNumeratorNormal t (0, 1)) (realPoint b) := by
  have hp := quartic_bernstein_nonneg (axisVOrderPoly a b) l u hc t hlt htu
  rw [axis_v_order_poly_eval] at hp
  linarith

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.axis_u_order_of_bernstein
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.axis_v_order_of_bernstein
