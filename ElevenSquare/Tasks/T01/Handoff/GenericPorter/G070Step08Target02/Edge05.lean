import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Data

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Edge05
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem turn_checked : turn5.BernsteinPosCheck (15/32) (19/32) := by
  norm_num [turn5, Quartic.BernsteinPosCheck, Quartic.bernsteinOn,
    Quartic.shift, Quartic.toBernstein]

theorem edge_scaled (t : ℝ) :
    symbolicFacetReal f5 t = (realEdge (v5 t) (v6 t)).scale (1+t^2) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  ext <;> simp only [symbolicFacetReal, f5, SymbolicQuadratic.eval,
    RealHalfplane.scale, realEdge, v5, v6, k3, k4,
    ab3,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  all_goals push_cast
  all_goals field_simp [hd]
  all_goals ring

theorem turn_formula (t : ℝ) :
    turn5.eval t = (1+t^2)^2 *
      baselineCross (v6 t - v5 t) (v4 t - v5 t) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  simp only [turn5, Quartic.eval, baselineCross, v5, v6, v4,
    k3, k4,
    ab2, ab3,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  push_cast
  field_simp [hd]
  ring

theorem turn_positive (t : ℝ) (hl : ((15/32 : ℚ) : ℝ) ≤ t)
    (hu : t ≤ ((19/32 : ℚ) : ℝ)) :
    0 < baselineCross (v6 t - v5 t) (v4 t - v5 t) := by
  have h := quartic_bernstein_pos turn5 (15/32) (19/32) turn_checked t hl hu
  rw [turn_formula] at h
  have hd : 0 < (1+t^2)^2 := by positivity
  exact (mul_pos_iff_of_pos_left hd).mp h

#print axioms edge_scaled
#print axioms turn_positive

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Edge05
