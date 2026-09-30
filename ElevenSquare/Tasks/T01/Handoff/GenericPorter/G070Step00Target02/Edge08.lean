import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Data

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge08
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem turn_checked : turn8.BernsteinPosCheck (1/32) (5/128) := by
  norm_num [turn8, Quartic.BernsteinPosCheck, Quartic.bernsteinOn,
    Quartic.shift, Quartic.toBernstein]

theorem edge_scaled (t : ℝ) :
    symbolicFacetReal f8 t = (realEdge (v8 t) (v9 t)).scale (1+t^2) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  ext <;> simp only [symbolicFacetReal, f8, SymbolicQuadratic.eval,
    RealHalfplane.scale, realEdge, v8, v9, k5, k6,
    ab0,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  all_goals push_cast
  all_goals field_simp [hd]
  all_goals ring

theorem turn_formula (t : ℝ) :
    turn8.eval t = (1+t^2)^2 *
      baselineCross (v9 t - v8 t) (v7 t - v8 t) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  simp only [turn8, Quartic.eval, baselineCross, v8, v9, v7,
    k5, k6,
    ab0, ab3,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  push_cast
  field_simp [hd]
  ring

theorem turn_positive (t : ℝ) (hl : ((1/32 : ℚ) : ℝ) ≤ t)
    (hu : t ≤ ((5/128 : ℚ) : ℝ)) :
    0 < baselineCross (v9 t - v8 t) (v7 t - v8 t) := by
  have h := quartic_bernstein_pos turn8 (1/32) (5/128) turn_checked t hl hu
  rw [turn_formula] at h
  have hd : 0 < (1+t^2)^2 := by positivity
  exact (mul_pos_iff_of_pos_left hd).mp h

#print axioms edge_scaled
#print axioms turn_positive

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target02.Edge08
