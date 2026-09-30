import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable21
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable21_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0) ≤ ((49095291 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((335241 / 200000) : ℝ) := by
    rw [concreteUnavailable21_A0, concreteUnavailable21_A1]
    exact (add_le_add concrete_abs_poly008 concrete_abs_poly036).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable21_L0, concreteUnavailable21_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 10 0) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 10 0)) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable21_C0, concreteUnavailable21_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((335241 / 200000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0 ≤ ((335241 / 200000)+1*((1920157 / 2500000000)+(8962451 / 10000000000)+((8222903 / 2500000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)^2+2*(1*((1920157 / 2500000000)+(8962451 / 10000000000)+((8222903 / 2500000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)+(191 / 250)*((67647473 / 10000000000)+(5670363 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable21_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 ≤ ((-44817907 / 20000000) : ℝ) := by
    rw [concreteUnavailable21_value]
    have hp := concrete_poly_upper_bound (![(-31 / 20), (-61 / 20), (11 / 5), (33 / 10), (-3 / 4), (-71 / 20), (5 / 2), (-1 / 2)]) ((-44817907 / 20000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable21_L0, concreteUnavailable21_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((63991711 / 100000000) : ℝ) := by
    rw [concreteUnavailable21_A1]
    exact concrete_abs_poly036
  have hC : |dot (perp (cornerOffset constructionSquare 10 0)) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable21_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((-44817907 / 20000000)) (1) ((63991711 / 100000000)) ((5939131 / 100000000)) ((49095291 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable21_curvature ?_ h hh
  change (-44817907 / 20000000)+1*((1920157 / 2500000000)+(8962451 / 10000000000)+((8222903 / 2500000000)+(5212397 / 5000000000)))+(5670363 / 2500000000)*(63991711 / 100000000)+((67647473 / 10000000000)+(5670363 / 2500000000))*(5939131 / 100000000)+(49095291 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
