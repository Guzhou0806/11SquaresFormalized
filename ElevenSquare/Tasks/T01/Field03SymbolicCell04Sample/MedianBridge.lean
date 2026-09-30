import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.Data
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisUHi
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisVLo
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisVHi
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.FixedOrders
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianConcreteSupport
import ElevenSquare.Tasks.T01.Field03Feature

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def medianHalfwidth : ℝ := 49999 / 100000

private theorem sites_eq :
    ({site0, site1, site2} : Finset QPoint) = baselineField03Sites := by
  norm_num [site0, site1, site2, baselineField03Sites]

private theorem site0_median_u (t : ℝ)
    (horder : dot (chartNumeratorNormal t (1,0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site1)) :
    MedianLowerBound ({site0, site1, site2} : Finset QPoint) 2
      (fun p => dot (chartNumeratorNormal t (1,0)) (realPoint p))
      (dot (chartNumeratorNormal t (1,0)) (realPoint site0)) := by
  exact median_lower_bound_three_of_one_above site0 site1 site2
      (fun p => dot (chartNumeratorNormal t (1,0)) (realPoint p)) horder

private theorem site0_median_uminus (t : ℝ)
    (horder : dot (chartNumeratorNormal t (1,0)) (realPoint site2) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site0)) :
    MedianLowerBound ({site0,site1,site2} : Finset QPoint) 2
      (fun p => dot (chartNumeratorNormal t (-1,0)) (realPoint p))
      (dot (chartNumeratorNormal t (-1,0)) (realPoint site0)) := by
  have h0 := chart_neg_world_dot t (1,0) site0
  have h2 := chart_neg_world_dot t (1,0) site2
  norm_num [negPoint] at h0 h2
  have hup : dot (chartNumeratorNormal t (-1,0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (-1,0)) (realPoint site2) := by
    rw [h0, h2]
    linarith
  have hm := median_lower_bound_three_of_one_above site0 site2 site1
    (fun p => dot (chartNumeratorNormal t (-1,0)) (realPoint p)) hup
  convert hm using 1
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem site0_median_v (t : ℝ)
    (horder : dot (chartNumeratorNormal t (0,1)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (0,1)) (realPoint site2)) :
    MedianLowerBound ({site0,site1,site2} : Finset QPoint) 2
      (fun p => dot (chartNumeratorNormal t (0,1)) (realPoint p))
      (dot (chartNumeratorNormal t (0,1)) (realPoint site0)) := by
  have hm := median_lower_bound_three_of_one_above site0 site2 site1
    (fun p => dot (chartNumeratorNormal t (0,1)) (realPoint p)) horder
  convert hm using 1
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem site0_median_vminus (t : ℝ)
    (horder : dot (chartNumeratorNormal t (0,1)) (realPoint site1) ≤
      dot (chartNumeratorNormal t (0,1)) (realPoint site0)) :
    MedianLowerBound ({site0,site1,site2} : Finset QPoint) 2
      (fun p => dot (chartNumeratorNormal t (0,-1)) (realPoint p))
      (dot (chartNumeratorNormal t (0,-1)) (realPoint site0)) := by
  have h0 := chart_neg_world_dot t (0,1) site0
  have h1 := chart_neg_world_dot t (0,1) site1
  norm_num [negPoint] at h0 h1
  have hup : dot (chartNumeratorNormal t (0,-1)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (0,-1)) (realPoint site1) := by
    rw [h0, h1]
    linarith
  exact median_lower_bound_three_of_one_above site0 site1 site2
    (fun p => dot (chartNumeratorNormal t (0,-1)) (realPoint p)) hup

theorem target00_u_pos_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[0]'(by decide) ∈ target)
    (horder : dot (chartNumeratorNormal t (1,0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site1)) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (1,0) target := by
  let f : SymbolicFacet := target00[0]'(by decide)
  refine ⟨f, ?_, 1,
    dot (chartNumeratorNormal t (1,0)) (realPoint site0),
    by norm_num, ?_, ?_, ?_, site0_median_u t horder⟩
  · exact hmem
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
    ring
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
  · dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartNumeratorNormal, chartDenom, realPoint, site0, dot]
    push_cast
    norm_num
    nlinarith

theorem target00_u_neg_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[1]'(by decide) ∈ target)
    (horder : dot (chartNumeratorNormal t (1,0)) (realPoint site2) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site0)) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (-1,0) target := by
  let f : SymbolicFacet := target00[1]'(by decide)
  refine ⟨f, ?_, 1,
    dot (chartNumeratorNormal t (-1,0)) (realPoint site0),
    by norm_num, ?_, ?_, ?_, site0_median_uminus t horder⟩
  · exact hmem
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
    ring
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
  · dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartNumeratorNormal, chartDenom, realPoint, site0, dot]
    push_cast
    norm_num
    nlinarith

theorem target00_v_pos_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[2]'(by decide) ∈ target)
    (horder : dot (chartNumeratorNormal t (0,1)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (0,1)) (realPoint site2)) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (0,1) target := by
  let f : SymbolicFacet := target00[2]'(by decide)
  refine ⟨f, ?_, 1,
    dot (chartNumeratorNormal t (0,1)) (realPoint site0),
    by norm_num, ?_, ?_, ?_, site0_median_v t horder⟩
  · exact hmem
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
    ring
  · dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartNumeratorNormal, chartDenom, realPoint, site0, dot]
    push_cast
    norm_num
    nlinarith

theorem target00_v_neg_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[3]'(by decide) ∈ target)
    (horder : dot (chartNumeratorNormal t (0,1)) (realPoint site1) ≤
      dot (chartNumeratorNormal t (0,1)) (realPoint site0)) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (0,-1) target := by
  let f : SymbolicFacet := target00[3]'(by decide)
  refine ⟨f, ?_, 1,
    dot (chartNumeratorNormal t (0,-1)) (realPoint site0),
    by norm_num, ?_, ?_, ?_, site0_median_vminus t horder⟩
  · exact hmem
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
  · norm_num [f, target00, SymbolicQuadratic.eval,
      chartNumeratorNormal]
    ring
  · dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartNumeratorNormal, chartDenom, realPoint, site0, dot]
    push_cast
    norm_num
    nlinarith

theorem target00_pair01_pos_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[4]'(by decide) ∈ target)
    (ha : q.axis = chartAxis t) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (pairPerp q site0 site1) target := by
  let f : SymbolicFacet := target00[4]'(by decide)
  let n := pairPerp q site0 site1
  let bound := dot (chartNumeratorNormal t n) (realPoint site0)
  refine ⟨f, ?_, 1, bound, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hmem
  · rw [chart_pair_perp_world_normal q t ha site0 site1]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site1]
    ring
  · rw [chart_pair_perp_world_normal q t ha site0 site1]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site1]
    ring
  · have habs := chart_pair_perp_local_abs_support q t ha site0 site1
    have hworld := chart_pair_world_projection q t ha site0 site1 site0
    dsimp [n, bound]
    rw [hworld, mul_assoc, habs]
    let X : ℝ := ((site1.2 : ℝ) - (site0.2 : ℝ)) * (1 - t ^ 2) +
        ((site0.1 : ℝ) - (site1.1 : ℝ)) * (2 * t)
    let Y : ℝ := -((site1.2 : ℝ) - (site0.2 : ℝ)) * (2 * t) +
        ((site0.1 : ℝ) - (site1.1 : ℝ)) * (1 - t ^ 2)
    have hx : -X ≤ |X| := neg_le_abs X
    have hy : -Y ≤ |Y| := neg_le_abs Y
    dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site0, site1] at *
    push_cast at *
    nlinarith
  · have horder :
        dot (fixedPairNormal site0 site1) (realPoint site0) ≤
          dot (fixedPairNormal site0 site1) (realPoint site1) := by
      change dot fixed01 (realPoint site0) ≤ dot fixed01 (realPoint site1)
      exact le_of_eq fixed01_order.2
    exact pair_median_of_fixed_order q t ha site0 site1 site0 site1 site2 horder

theorem target00_pair01_neg_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[5]'(by decide) ∈ target)
    (ha : q.axis = chartAxis t) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (negPoint (pairPerp q site0 site1)) target := by
  let f : SymbolicFacet := target00[5]'(by decide)
  let n := negPoint (pairPerp q site0 site1)
  let bound := dot (chartNumeratorNormal t n) (realPoint site0)
  refine ⟨f, ?_, 1, bound, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hmem
  · rw [chart_neg_pair_perp_world_normal q t ha site0 site1]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site1]
    ring
  · rw [chart_neg_pair_perp_world_normal q t ha site0 site1]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site0, site1]
    ring
  · have habs := chart_neg_pair_perp_local_abs_support q t ha site0 site1
    have hworld := chart_neg_pair_world_projection q t ha site0 site1 site0
    dsimp [n, bound]
    rw [hworld, mul_assoc, habs]
    let X : ℝ := ((site1.2 : ℝ) - (site0.2 : ℝ)) * (1 - t ^ 2) +
        ((site0.1 : ℝ) - (site1.1 : ℝ)) * (2 * t)
    let Y : ℝ := -((site1.2 : ℝ) - (site0.2 : ℝ)) * (2 * t) +
        ((site0.1 : ℝ) - (site1.1 : ℝ)) * (1 - t ^ 2)
    have hx : -X ≤ |X| := neg_le_abs X
    have hy : -Y ≤ |Y| := neg_le_abs Y
    dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site0, site1] at *
    push_cast at *
    nlinarith
  · have horder :
        dot (fixedPairNormal site0 site1) (realPoint site2) ≤
          dot (fixedPairNormal site0 site1) (realPoint site0) := by
      change dot fixed01 (realPoint site2) ≤ dot fixed01 (realPoint site0)
      exact fixed01_order.1
    have hm := neg_pair_median_of_fixed_order q t ha site0 site1 site0 site2 site1
      horder
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
    have hy : Y ≤ |Y| := le_abs_self Y
    dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site0, site2, site2] at *
    push_cast at *
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
    have hy : Y ≤ |Y| := le_abs_self Y
    dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site0, site2, site2] at *
    push_cast at *
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

theorem target00_pair12_pos_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[8]'(by decide) ∈ target)
    (ha : q.axis = chartAxis t) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (pairPerp q site1 site2) target := by
  let f : SymbolicFacet := target00[8]'(by decide)
  let n := pairPerp q site1 site2
  let bound := dot (chartNumeratorNormal t n) (realPoint site1)
  refine ⟨f, ?_, 1, bound, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hmem
  · rw [chart_pair_perp_world_normal q t ha site1 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site1, site2] <;> ring
  · rw [chart_pair_perp_world_normal q t ha site1 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site1, site2] <;> ring
  · have habs := chart_pair_perp_local_abs_support q t ha site1 site2
    have hworld := chart_pair_world_projection q t ha site1 site2 site1
    dsimp [n, bound]
    rw [hworld, mul_assoc, habs]
    let X : ℝ := ((site2.2 : ℝ) - (site1.2 : ℝ)) * (1 - t ^ 2) +
        ((site1.1 : ℝ) - (site2.1 : ℝ)) * (2 * t)
    let Y : ℝ := -((site2.2 : ℝ) - (site1.2 : ℝ)) * (2 * t) +
        ((site1.1 : ℝ) - (site2.1 : ℝ)) * (1 - t ^ 2)
    have hx : X ≤ |X| := le_abs_self X
    have hy : Y ≤ |Y| := le_abs_self Y
    dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site1, site2, site1] at *
    push_cast at *
    nlinarith
  · have horder :
        dot (fixedPairNormal site1 site2) (realPoint site1) ≤
          dot (fixedPairNormal site1 site2) (realPoint site2) := by
      change dot fixed12 (realPoint site1) ≤ dot fixed12 (realPoint site2)
      exact le_of_eq fixed12_order.2
    have hm := pair_median_of_fixed_order q t ha site1 site2 site1 site2 site0
      horder
    convert hm using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem target00_pair12_neg_witness (q : UnitSquare) (t : ℝ)
    (target : List SymbolicFacet)
    (hmem : target00[9]'(by decide) ∈ target)
    (ha : q.axis = chartAxis t) :
    SymbolicMedianFacetWitness ({site0,site1,site2} : Finset QPoint) 2
      q t medianHalfwidth (negPoint (pairPerp q site1 site2)) target := by
  let f : SymbolicFacet := target00[9]'(by decide)
  let n := negPoint (pairPerp q site1 site2)
  let bound := dot (chartNumeratorNormal t n) (realPoint site1)
  refine ⟨f, ?_, 1, bound, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hmem
  · rw [chart_neg_pair_perp_world_normal q t ha site1 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site1, site2] <;> ring
  · rw [chart_neg_pair_perp_world_normal q t ha site1 site2]
    norm_num [f, target00, SymbolicQuadratic.eval,
      chartDenom, site1, site2] <;> ring
  · have habs := chart_neg_pair_perp_local_abs_support q t ha site1 site2
    have hworld := chart_neg_pair_world_projection q t ha site1 site2 site1
    dsimp [n, bound]
    rw [hworld, mul_assoc, habs]
    let X : ℝ := ((site2.2 : ℝ) - (site1.2 : ℝ)) * (1 - t ^ 2) +
        ((site1.1 : ℝ) - (site2.1 : ℝ)) * (2 * t)
    let Y : ℝ := -((site2.2 : ℝ) - (site1.2 : ℝ)) * (2 * t) +
        ((site1.1 : ℝ) - (site2.1 : ℝ)) * (1 - t ^ 2)
    have hx : X ≤ |X| := le_abs_self X
    have hy : Y ≤ |Y| := le_abs_self Y
    dsimp [f, target00, SymbolicQuadratic.eval, medianHalfwidth,
      chartDenom, fixedPairNormal, realPoint, dot, X, Y,
      site1, site2, site1] at *
    push_cast at *
    nlinarith
  · have horder :
        dot (fixedPairNormal site1 site2) (realPoint site0) ≤
          dot (fixedPairNormal site1 site2) (realPoint site1) := by
      change dot fixed12 (realPoint site0) ≤ dot fixed12 (realPoint site1)
      exact fixed12_order.1
    have hm := neg_pair_median_of_fixed_order q t ha site1 site2 site1 site0 site2
      horder
    convert hm using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Every pose whose center lies in the sample TRUE symbolic polygon strictly
    captures two of the three field-feature sites. -/
theorem target00_majority_of_orders (q : UnitSquare) (t : ℝ)
    (huhi : dot (chartNumeratorNormal t (1,0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site1))
    (hulo : dot (chartNumeratorNormal t (1,0)) (realPoint site2) ≤
      dot (chartNumeratorNormal t (1,0)) (realPoint site0))
    (hvhi : dot (chartNumeratorNormal t (0,1)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (0,1)) (realPoint site2))
    (hvlo : dot (chartNumeratorNormal t (0,1)) (realPoint site1) ≤
      dot (chartNumeratorNormal t (0,1)) (realPoint site0))
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
    · exact target00_u_pos_witness q t target00 (by simp [target00]) (huhi)
    · exact target00_u_neg_witness q t target00 (by simp [target00]) (hulo)
    · exact target00_v_pos_witness q t target00 (by simp [target00]) (hvhi)
    · exact target00_v_neg_witness q t target00 (by simp [target00]) (hvlo)
    · exact target00_pair01_pos_witness q t target00 (by simp [target00]) ha
    · exact target00_pair01_neg_witness q t target00 (by simp [target00]) ha
    · exact target00_pair02_pos_witness q t target00 (by simp [target00]) ha
    · exact target00_pair02_neg_witness q t target00 (by simp [target00]) ha
    · exact target00_pair12_pos_witness q t target00 (by simp [target00]) ha
    · exact target00_pair12_neg_witness q t target00 (by simp [target00]) ha
  rwa [sites_eq] at hm


theorem target00_majority (q : UnitSquare) (t : ℝ)
    (hlo : ((1/256 : ℚ) : ℝ) ≤ t) (hhi : t ≤ ((1/128 : ℚ) : ℝ))
    (ha : q.axis = chartAxis t)
    (hcontains : SymbolicPolygonContains target00 t q.center) :
    BaselineMajorityCapture baselineField03Sites 2 q :=
  target00_majority_of_orders q t (uhi_order t hlo hhi)
    (ulo_order t hlo hhi) (vhi_order t hlo hhi) (vlo_order t hlo hhi)
    ha hcontains

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_u_pos_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_u_neg_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_v_pos_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_v_neg_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_pair01_pos_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_pair01_neg_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_pair02_pos_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_pair02_neg_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_pair12_pos_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_pair12_neg_witness
#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_majority

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.target00_majority_of_orders
