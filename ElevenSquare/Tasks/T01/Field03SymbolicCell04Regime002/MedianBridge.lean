import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Data
import ElevenSquare.Tasks.T01.Field03SymbolicMedianRep002
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.MedianBridge
import ElevenSquare.Tasks.T01.Field03Feature

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Tasks.T01.Field03SymbolicMedianRep002
noncomputable section

private theorem sites_eq :
    ({site0,site1,site2} : Finset QPoint) = baselineField03Sites := by
  norm_num [site0, site1, site2, baselineField03Sites]

theorem target00_u_pos_witness (q : UnitSquare) (t : ℝ)
    (horder : dot (chartNumeratorNormal t (1,0)) (realPoint site2) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site1)) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (1,0) target00 := by
  let f : SymbolicFacet := target00[0]'(by decide)
  refine ⟨f, ?_, 1,
    dot (chartNumeratorNormal t (1,0)) (realPoint site2),
    by norm_num, ?_, ?_, ?_, ?_⟩
  · simp [f, target00]
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
    ring
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
  · dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartNumeratorNormal, chartDenom, realPoint, site2, dot]
    push_cast
    norm_num
    nlinarith
  · have hm := median_lower_bound_three_of_one_above site2 site1
      site0 (fun p => dot (chartNumeratorNormal t (1,0)) (realPoint p)) horder
    convert hm using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
theorem target00_u_neg_witness (q : UnitSquare) (t : ℝ)
    (horder : dot (chartNumeratorNormal t (1,0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site2)) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (-1,0) target00 := by
  let f : SymbolicFacet := target00[1]'(by decide)
  refine ⟨f, ?_, 1,
    dot (chartNumeratorNormal t (-1,0)) (realPoint site2),
    by norm_num, ?_, ?_, ?_, ?_⟩
  · simp [f, target00]
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
    ring
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
  · dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartNumeratorNormal, chartDenom, realPoint, site2, dot]
    push_cast
    norm_num
    nlinarith
  · have hmid := chart_neg_world_dot t (1,0) site2
    have hlow := chart_neg_world_dot t (1,0) site0
    norm_num [negPoint] at hmid hlow
    have hup : dot (chartNumeratorNormal t (-1,0)) (realPoint site2) ≤
        dot (chartNumeratorNormal t (-1,0)) (realPoint site0) := by
      rw [hmid, hlow]
      linarith
    have hm := median_lower_bound_three_of_one_above site2 site0
      site1 (fun p => dot (chartNumeratorNormal t (-1,0)) (realPoint p)) hup
    convert hm using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem target00_pair02_pos_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[6]'(by decide) ∈ target)
    (ha : q.axis = chartAxis t) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (pairPerp q site0 site2) target := by
  let f : SymbolicFacet := target00[6]'(by decide)
  let n := pairPerp q site0 site2
  let bound := dot (chartNumeratorNormal t n) (realPoint site2)
  refine ⟨f, ?_, 1, bound, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hmem
  · rw [chart_pair_perp_world_normal q t ha site0 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site2] <;> ring
  · rw [chart_pair_perp_world_normal q t ha site0 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site2] <;> ring
  · have habs := chart_pair_perp_local_abs_support q t ha site0 site2
    have hworld := chart_pair_world_projection q t ha site0 site2 site2
    dsimp [n, bound]
    rw [hworld, mul_assoc, habs]
    let X : ℝ := ((site2.2 : ℝ) - (site0.2 : ℝ)) * (1 - t ^ 2) +
        ((site0.1 : ℝ) - (site2.1 : ℝ)) * (2 * t)
    let Y : ℝ := -((site2.2 : ℝ) - (site0.2 : ℝ)) * (2 * t) +
        ((site0.1 : ℝ) - (site2.1 : ℝ)) * (1 - t ^ 2)
    have hx : X ≤ |X| := le_abs_self X
    have hy : -Y ≤ |Y| := neg_le_abs Y
    norm_num [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site0, site2, site2] at hx hy ⊢
    nlinarith
  · have horder :
        dot (fixedPairNormal site0 site2) (realPoint site2) ≤
          dot (fixedPairNormal site0 site2) (realPoint site1) := by
      change dot fixed02 (realPoint site2) ≤ dot fixed02 (realPoint site1)
      exact fixed02_order.2
    have hm := pair_median_of_fixed_order q t ha site0 site2 site2 site1 site0
      horder
    convert hm using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem target00_pair02_neg_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[7]'(by decide) ∈ target)
    (ha : q.axis = chartAxis t) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (negPoint (pairPerp q site0 site2)) target := by
  let f : SymbolicFacet := target00[7]'(by decide)
  let n := negPoint (pairPerp q site0 site2)
  let bound := dot (chartNumeratorNormal t n) (realPoint site2)
  refine ⟨f, ?_, 1, bound, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hmem
  · rw [chart_neg_pair_perp_world_normal q t ha site0 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site2] <;> ring
  · rw [chart_neg_pair_perp_world_normal q t ha site0 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site2] <;> ring
  · have habs := chart_neg_pair_perp_local_abs_support q t ha site0 site2
    have hworld := chart_neg_pair_world_projection q t ha site0 site2 site2
    dsimp [n, bound]
    rw [hworld, mul_assoc, habs]
    let X : ℝ := ((site2.2 : ℝ) - (site0.2 : ℝ)) * (1 - t ^ 2) +
        ((site0.1 : ℝ) - (site2.1 : ℝ)) * (2 * t)
    let Y : ℝ := -((site2.2 : ℝ) - (site0.2 : ℝ)) * (2 * t) +
        ((site0.1 : ℝ) - (site2.1 : ℝ)) * (1 - t ^ 2)
    have hx : X ≤ |X| := le_abs_self X
    have hy : -Y ≤ |Y| := neg_le_abs Y
    norm_num [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site0, site2, site2] at hx hy ⊢
    nlinarith
  · have horder :
        dot (fixedPairNormal site0 site2) (realPoint site0) ≤
          dot (fixedPairNormal site0 site2) (realPoint site2) := by
      change dot fixed02 (realPoint site0) ≤ dot fixed02 (realPoint site2)
      exact le_of_eq fixed02_order.1
    have hm := neg_pair_median_of_fixed_order q t ha site0 site2 site2 site0 site1
      horder
    convert hm using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem target00_majority (q : UnitSquare) (t : ℝ)
    (hlo : ((619/4096 : ℚ) : ℝ) ≤ t) (hhi : t ≤ ((897/2048 : ℚ) : ℝ))
    (ha : q.axis = chartAxis t)
    (hcontains : SymbolicPolygonContains target00 t q.center) :
    BaselineMajorityCapture baselineField03Sites 2 q := by
  have hm : BaselineMajorityCapture ({site0,site1,site2} : Finset QPoint) 2 q := by
    apply symbolic_triple_median_target_majority site0 site1 site2
      (by norm_num [site0, site1]) (by norm_num [site0, site2])
      (by norm_num [site1, site2]) q t medianHalfwidth
      (by norm_num [medianHalfwidth]) ha target00 hcontains
    intro normal hn
    simp [tripleMedianNormals] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact target00_u_pos_witness q t (UHi_order t hlo hhi)
    · exact target00_u_neg_witness q t (ULo_order t hlo hhi)
    · exact Field03SymbolicCell04Sample.target00_v_pos_witness q t target00 (by simp [target00, Field03SymbolicCell04Sample.target00]) (VHi_order t hlo hhi)
    · exact Field03SymbolicCell04Sample.target00_v_neg_witness q t target00 (by simp [target00, Field03SymbolicCell04Sample.target00]) (VLo_order t hlo hhi)
    · exact Field03SymbolicCell04Sample.target00_pair01_pos_witness q t target00 (by simp [target00, Field03SymbolicCell04Sample.target00]) ha
    · exact Field03SymbolicCell04Sample.target00_pair01_neg_witness q t target00 (by simp [target00, Field03SymbolicCell04Sample.target00]) ha
    · exact target00_pair02_pos_witness q t target00 (by simp [target00]) ha
    · exact target00_pair02_neg_witness q t target00 (by simp [target00]) ha
    · exact Field03SymbolicCell04Sample.target00_pair12_pos_witness q t target00 (by simp [target00, Field03SymbolicCell04Sample.target00]) ha
    · exact Field03SymbolicCell04Sample.target00_pair12_neg_witness q t target00 (by simp [target00, Field03SymbolicCell04Sample.target00]) ha
  rwa [sites_eq] at hm

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.target00_majority
