import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target01.Data

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target01.Edge01
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target01
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem turn_checked : turn1.BernsteinPosCheck (1/32) (5/128) := by
  norm_num [turn1, Quartic.BernsteinPosCheck, Quartic.bernsteinOn,
    Quartic.shift, Quartic.toBernstein]

theorem edge_scaled (t : ℝ) :
    symbolicFacetReal f1 t = (realEdge (v1 t) (v2 t)).scale (1+t^2) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  ext <;> simp only [symbolicFacetReal, f1, SymbolicQuadratic.eval,
    RealHalfplane.scale, realEdge, v1, v2, k0, k1,
    ab2,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  all_goals push_cast
  all_goals field_simp [hd]
  all_goals ring

theorem turn_formula (t : ℝ) :
    turn1.eval t = (1+t^2)^2 *
      baselineCross (v2 t - v1 t) (v0 t - v1 t) := by
  have hd : 1+t^2 ≠ 0 := by positivity
  simp only [turn1, Quartic.eval, baselineCross, v1, v2, v0,
    k0, k1,
    ab1, ab2,
    chartLocalOffset, realPoint, Prod.fst_sub, Prod.snd_sub]
  push_cast
  field_simp [hd] <;> ring

theorem turn_positive (t : ℝ) (hl : ((1/32 : ℚ) : ℝ) ≤ t)
    (hu : t ≤ ((5/128 : ℚ) : ℝ)) :
    0 < baselineCross (v2 t - v1 t) (v0 t - v1 t) := by
  have h := quartic_bernstein_pos turn1 (1/32) (5/128) turn_checked t hl hu
  rw [turn_formula] at h
  have hd : 0 < (1+t^2)^2 := by positivity
  exact (mul_pos_iff_of_pos_left hd).mp h

#print axioms edge_scaled
#print axioms turn_positive

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Target01.Edge01
