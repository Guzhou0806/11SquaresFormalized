import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable84
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable84_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((51183607 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((83361 / 62500) : ℝ) := by
    rw [concreteUnavailable84_A0, concreteUnavailable84_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly033).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable84_L0, concreteUnavailable84_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 10 1) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 10 1)) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable84_C0, concreteUnavailable84_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((83361 / 62500)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((83361 / 62500)+(1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+1*((67647473 / 10000000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable84_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ (-2 : ℝ) := by
    rw [concreteUnavailable84_value]
    have hp := concrete_poly_upper_bound (![-2, 0, 0, 0, 0, 0, 0, 0]) (-2)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable84_L0, concreteUnavailable84_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((33377597 / 100000000) : ℝ) := by
    rw [concreteUnavailable84_A1]
    exact concrete_abs_poly033
  have hC : |dot (perp (cornerOffset constructionSquare 10 1)) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable84_C1]
    exact concrete_abs_poly058
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := true }) 1
    (-2) ((1409217 / 1000000)) ((33377597 / 100000000)) ((1 / 2)) ((51183607 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable84_curvature ?_ h hh
  change -2+(1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000)))+(40352153 / 10000000000)*(33377597 / 100000000)+((67647473 / 10000000000)+(40352153 / 10000000000))*(1 / 2)+(51183607 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
