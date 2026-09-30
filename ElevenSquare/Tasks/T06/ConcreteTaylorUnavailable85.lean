import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable85
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly07
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable85_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) ≤ ((72275923 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((83361 / 62500) : ℝ) := by
    rw [concreteUnavailable85_A0, concreteUnavailable85_A1]
    exact (add_le_add concrete_abs_poly031 concrete_abs_poly072).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable85_L0, concreteUnavailable85_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 2) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 9 2)) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable85_C0, concreteUnavailable85_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((83361 / 62500)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 ≤ ((83361 / 62500)+(1409217 / 1000000)*((293551 / 400000000)+(1920157 / 2500000000)+((10335557 / 10000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)^2+2*((1409217 / 1000000)*((293551 / 400000000)+(1920157 / 2500000000)+((10335557 / 10000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)+1*((40352153 / 10000000000)+(67647473 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable85_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 ≤ ((-66622403 / 100000000) : ℝ) := by
    rw [concreteUnavailable85_value]
    have hp := concrete_poly_upper_bound (![(-39 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)]) ((-66622403 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable85_L0, concreteUnavailable85_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable85_A1]
    exact concrete_abs_poly072
  have hC : |dot (perp (cornerOffset constructionSquare 9 2)) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable85_C1]
    exact concrete_abs_poly058
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 10, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((-66622403 / 100000000)) ((1409217 / 1000000)) (1) ((1 / 2)) ((72275923 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable85_curvature ?_ h hh
  change (-66622403 / 100000000)+(1409217 / 1000000)*((293551 / 400000000)+(1920157 / 2500000000)+((10335557 / 10000000000)+(8222903 / 2500000000)))+(67647473 / 10000000000)*1+((40352153 / 10000000000)+(67647473 / 10000000000))*(1 / 2)+(72275923 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
