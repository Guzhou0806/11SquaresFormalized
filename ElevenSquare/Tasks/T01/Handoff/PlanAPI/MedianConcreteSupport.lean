import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianWorldBridge

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- A three-site lower median needs only one other site whose projection is
    at least the proposed median. The third site may lie anywhere. -/
theorem median_lower_bound_three_of_one_above
    (middle upper lower : QPoint) (projection : QPoint → ℝ)
    (hupper : projection middle ≤ projection upper) :
    MedianLowerBound ({middle, upper, lower} : Finset QPoint) 2
      projection (projection middle) := by
  classical
  unfold MedianLowerBound
  have hsubset :
      ({middle, upper, lower} : Finset QPoint).filter
        (fun p => projection p < projection middle) ⊆ {lower} := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hp ⊢
    rcases hp.1 with rfl | rfl | rfl
    · exact (False.elim ((lt_irrefl _).elim hp.2))
    · exact (False.elim ((not_lt_of_ge hupper) hp.2))
    · rfl
  have hcard := Finset.card_le_card hsubset
  simp only [Finset.card_singleton] at hcard
  omega

theorem chart_neg_world_dot (t : ℝ) (normal : Point) (p : QPoint) :
    dot (chartNumeratorNormal t (negPoint normal)) (realPoint p) =
      -dot (chartNumeratorNormal t normal) (realPoint p) := by
  dsimp [chartNumeratorNormal, negPoint, dot]
  ring

/-- Clearing the rational angle chart makes the local normal perpendicular
    to a site pair independent of angle. -/
theorem chart_pair_perp_world_normal
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b : QPoint) :
    chartNumeratorNormal t (pairPerp q a b) =
      (chartDenom t * ((b.2 : ℝ) - (a.2 : ℝ)),
        chartDenom t * ((a.1 : ℝ) - (b.1 : ℝ))) := by
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + t ^ 2)
  dsimp [chartDenom, chartNumeratorNormal, pairPerp, pairDX, pairDY,
    localX, localY, dot, perp, realPoint]
  rw [ha]
  dsimp [chartAxis]
  ext <;> dsimp <;> field_simp [hd] <;> ring

theorem chart_neg_pair_perp_world_normal
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b : QPoint) :
    chartNumeratorNormal t (negPoint (pairPerp q a b)) =
      (chartDenom t * ((a.2 : ℝ) - (b.2 : ℝ)),
        chartDenom t * ((b.1 : ℝ) - (a.1 : ℝ))) := by
  have hp := chart_pair_perp_world_normal q t ha a b
  have hn (p : Point) :
      chartNumeratorNormal t (negPoint p) =
        negPoint (chartNumeratorNormal t p) := by
    apply Prod.ext <;> dsimp [chartNumeratorNormal, negPoint] <;> ring
  rw [hn, hp]
  apply Prod.ext <;> dsimp [negPoint] <;> ring

def fixedPairNormal (a b : QPoint) : Point :=
  ((b.2 : ℝ) - (a.2 : ℝ), (a.1 : ℝ) - (b.1 : ℝ))

theorem chart_pair_world_projection
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b p : QPoint) :
    dot (chartNumeratorNormal t (pairPerp q a b)) (realPoint p) =
      chartDenom t * dot (fixedPairNormal a b) (realPoint p) := by
  rw [chart_pair_perp_world_normal q t ha a b]
  dsimp [fixedPairNormal, dot]
  ring

theorem chart_neg_pair_world_projection
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b p : QPoint) :
    dot (chartNumeratorNormal t (negPoint (pairPerp q a b))) (realPoint p) =
      -(chartDenom t * dot (fixedPairNormal a b) (realPoint p)) := by
  rw [chart_neg_world_dot, chart_pair_world_projection q t ha a b p]

theorem pair_world_order
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b middle upper : QPoint)
    (horder : dot (fixedPairNormal a b) (realPoint middle) ≤
      dot (fixedPairNormal a b) (realPoint upper)) :
    dot (chartNumeratorNormal t (pairPerp q a b)) (realPoint middle) ≤
      dot (chartNumeratorNormal t (pairPerp q a b)) (realPoint upper) := by
  rw [chart_pair_world_projection q t ha a b,
    chart_pair_world_projection q t ha a b]
  exact mul_le_mul_of_nonneg_left horder (chartDenom_pos t).le

theorem neg_pair_world_order
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b middle upper : QPoint)
    (horder : dot (fixedPairNormal a b) (realPoint upper) ≤
      dot (fixedPairNormal a b) (realPoint middle)) :
    dot (chartNumeratorNormal t (negPoint (pairPerp q a b)))
      (realPoint middle) ≤
      dot (chartNumeratorNormal t (negPoint (pairPerp q a b)))
        (realPoint upper) := by
  rw [chart_neg_pair_world_projection q t ha a b,
    chart_neg_pair_world_projection q t ha a b]
  exact neg_le_neg (mul_le_mul_of_nonneg_left horder (chartDenom_pos t).le)

theorem pair_median_of_fixed_order
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b middle upper lower : QPoint)
    (horder : dot (fixedPairNormal a b) (realPoint middle) ≤
      dot (fixedPairNormal a b) (realPoint upper)) :
    MedianLowerBound ({middle,upper,lower} : Finset QPoint) 2
      (fun p => dot (chartNumeratorNormal t (pairPerp q a b))
        (realPoint p))
      (dot (chartNumeratorNormal t (pairPerp q a b))
        (realPoint middle)) :=
  median_lower_bound_three_of_one_above middle upper lower _
    (pair_world_order q t ha a b middle upper horder)

theorem neg_pair_median_of_fixed_order
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b middle upper lower : QPoint)
    (horder : dot (fixedPairNormal a b) (realPoint upper) ≤
      dot (fixedPairNormal a b) (realPoint middle)) :
    MedianLowerBound ({middle,upper,lower} : Finset QPoint) 2
      (fun p => dot (chartNumeratorNormal t
        (negPoint (pairPerp q a b))) (realPoint p))
      (dot (chartNumeratorNormal t
        (negPoint (pairPerp q a b))) (realPoint middle)) :=
  median_lower_bound_three_of_one_above middle upper lower _
    (neg_pair_world_order q t ha a b middle upper horder)

/-- The two local components of a pair-perpendicular normal are world
    projections on the numerator chart axes after clearing `1+t²`. -/
theorem chart_pair_perp_local_coordinates
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b : QPoint) :
    chartDenom t * (pairPerp q a b).1 =
        ((b.2 : ℝ) - (a.2 : ℝ)) * (1 - t ^ 2) +
          ((a.1 : ℝ) - (b.1 : ℝ)) * (2 * t) ∧
    chartDenom t * (pairPerp q a b).2 =
        -((b.2 : ℝ) - (a.2 : ℝ)) * (2 * t) +
          ((a.1 : ℝ) - (b.1 : ℝ)) * (1 - t ^ 2) := by
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + t ^ 2)
  constructor
  · dsimp [chartDenom, pairPerp, pairDY, localY, dot, perp, realPoint]
    rw [ha]
    dsimp [chartAxis]
    field_simp [hd]
    ring
  · dsimp [chartDenom, pairPerp, pairDX, localX, dot, realPoint]
    rw [ha]
    dsimp [chartAxis]
    field_simp [hd]
    ring

theorem chart_pair_perp_local_abs_support
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b : QPoint) :
    chartDenom t *
      (|(pairPerp q a b).1| + |(pairPerp q a b).2|) =
      |((b.2 : ℝ) - (a.2 : ℝ)) * (1 - t ^ 2) +
        ((a.1 : ℝ) - (b.1 : ℝ)) * (2 * t)| +
      |-((b.2 : ℝ) - (a.2 : ℝ)) * (2 * t) +
        ((a.1 : ℝ) - (b.1 : ℝ)) * (1 - t ^ 2)| := by
  obtain ⟨h1, h2⟩ := chart_pair_perp_local_coordinates q t ha a b
  have hd : 0 ≤ chartDenom t := (chartDenom_pos t).le
  calc
    chartDenom t *
        (|(pairPerp q a b).1| + |(pairPerp q a b).2|) =
        |chartDenom t * (pairPerp q a b).1| +
          |chartDenom t * (pairPerp q a b).2| := by
            rw [mul_add, abs_mul, abs_mul, abs_of_nonneg hd]
    _ = _ := by rw [h1, h2]

theorem chart_neg_pair_perp_local_abs_support
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (a b : QPoint) :
    chartDenom t *
      (|(negPoint (pairPerp q a b)).1| +
        |(negPoint (pairPerp q a b)).2|) =
      |((b.2 : ℝ) - (a.2 : ℝ)) * (1 - t ^ 2) +
        ((a.1 : ℝ) - (b.1 : ℝ)) * (2 * t)| +
      |-((b.2 : ℝ) - (a.2 : ℝ)) * (2 * t) +
        ((a.1 : ℝ) - (b.1 : ℝ)) * (1 - t ^ 2)| := by
  simpa [negPoint, abs_neg] using
    chart_pair_perp_local_abs_support q t ha a b

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.median_lower_bound_three_of_one_above
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.chart_pair_perp_world_normal
