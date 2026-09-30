import ElevenSquare.Pending.S07_ConvexSlices
import Mathlib.Tactic.LinearCombination

/-! Selected supporting halfplanes bound each vertical slab. The endpoint
identities and signs will be checked by exact integer certificates. -/
namespace ElevenSquare.Pending

theorem edge_interpolation_identity (A B C left right lo hi x y : ℝ)
    (hl : A*left+B*lo=C) (hr : A*right+B*hi=C) :
    B*((right-left)*y-((right-x)*lo+(x-left)*hi)) =
      (right-left)*(A*x+B*y-C) := by
  linear_combination -(right-x)*hl - (x-left)*hr

theorem lower_edge_bound (A B C left right lo hi x y : ℝ)
    (hw : left ≤ right) (hb : B < 0)
    (hl : A*left+B*lo=C) (hr : A*right+B*hi=C)
    (hp : A*x+B*y ≤ C) :
    (right-x)*lo+(x-left)*hi ≤ (right-left)*y := by
  have hn : B*((right-left)*y-((right-x)*lo+(x-left)*hi)) ≤ 0 := by
    rw [edge_interpolation_identity A B C left right lo hi x y hl hr]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw) (sub_nonpos.mpr hp)
  by_contra h
  have hd : (right-left)*y-((right-x)*lo+(x-left)*hi) < 0 := by linarith
  have := mul_pos_of_neg_of_neg hb hd
  linarith

theorem upper_edge_bound (A B C left right lo hi x y : ℝ)
    (hw : left ≤ right) (hb : 0 < B)
    (hl : A*left+B*lo=C) (hr : A*right+B*hi=C)
    (hp : A*x+B*y ≤ C) :
    (right-left)*y ≤ (right-x)*lo+(x-left)*hi := by
  have hn : B*((right-left)*y-((right-x)*lo+(x-left)*hi)) ≤ 0 := by
    rw [edge_interpolation_identity A B C left right lo hi x y hl hr]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw) (sub_nonpos.mpr hp)
  by_contra h
  have hd : 0 < (right-left)*y-((right-x)*lo+(x-left)*hi) := by linarith
  have := mul_pos hb hd
  linarith

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.lower_edge_bound
#print axioms ElevenSquare.Pending.upper_edge_bound
