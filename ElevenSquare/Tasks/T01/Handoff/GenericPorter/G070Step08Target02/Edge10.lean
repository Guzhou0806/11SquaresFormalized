import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Data

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Edge10
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem turn_checked : turn10.BernsteinPosCheck (15/32) (19/32) := by
  norm_num [turn10, Quartic.BernsteinPosCheck, Quartic.bernsteinOn,
    Quartic.shift, Quartic.toBernstein]

theorem edge_scaled (t : ℝ) :
    symbolicFacetReal f10 t = (realEdge (v10 t) (v11 t)).scale (1+t^2) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  ext <;> simp only [symbolicFacetReal, f10, SymbolicQuadratic.eval,
    RealHalfplane.scale, realEdge, v10, v11, k7,
    ab0, ab1,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  all_goals push_cast
  all_goals field_simp [hd]
  all_goals ring

theorem turn_formula (t : ℝ) :
    turn10.eval t = (1+t^2)^2 *
      baselineCross (v11 t - v10 t) (v9 t - v10 t) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  simp only [turn10, Quartic.eval, baselineCross, v10, v11, v9,
    k6, k7,
    ab0, ab1,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  push_cast
  field_simp [hd] <;> ring

theorem turn_positive (t : ℝ) (hl : ((15/32 : ℚ) : ℝ) ≤ t)
    (hu : t ≤ ((19/32 : ℚ) : ℝ)) :
    0 < baselineCross (v11 t - v10 t) (v9 t - v10 t) := by
  have h := quartic_bernstein_pos turn10 (15/32) (19/32) turn_checked t hl hu
  rw [turn_formula] at h
  have hd : 0 < (1+t^2)^2 := by positivity
  exact (mul_pos_iff_of_pos_left hd).mp h

#print axioms edge_scaled
#print axioms turn_positive

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Edge10
