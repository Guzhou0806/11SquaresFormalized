import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable82
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable82_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0) ≤ ((51183607 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((83361 / 62500) : ℝ) := by
    rw [concreteUnavailable82_A0, concreteUnavailable82_A1]
    exact (add_le_add concrete_abs_poly033 concrete_abs_poly003).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable82_L0, concreteUnavailable82_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 10 0) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 10 0)) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable82_C0, concreteUnavailable82_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((83361 / 62500)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0 ≤ ((83361 / 62500)+(1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+1*((67647473 / 10000000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable82_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 ≤ ((-66622403 / 100000000) : ℝ) := by
    rw [concreteUnavailable82_value]
    have hp := concrete_poly_upper_bound (![(-39 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)]) ((-66622403 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable82_L0, concreteUnavailable82_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable82_A1]
    exact concrete_abs_poly003
  have hC : |dot (perp (cornerOffset constructionSquare 10 0)) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable82_C1]
    exact concrete_abs_poly009
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((-66622403 / 100000000)) ((1409217 / 1000000)) (1) ((1 / 2)) ((51183607 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable82_curvature ?_ h hh
  change (-66622403 / 100000000)+(1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000)))+(40352153 / 10000000000)*1+((67647473 / 10000000000)+(40352153 / 10000000000))*(1 / 2)+(51183607 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
