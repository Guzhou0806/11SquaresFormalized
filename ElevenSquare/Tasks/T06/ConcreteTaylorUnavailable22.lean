import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable22
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable22_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }) 2) ≤ ((49095291 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((335241 / 200000) : ℝ) := by
    rw [concreteUnavailable22_A0, concreteUnavailable22_A1]
    exact (add_le_add concrete_abs_poly008 concrete_abs_poly036).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable22_L0, concreteUnavailable22_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 10 2) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 10 2)) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable22_C0, concreteUnavailable22_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((335241 / 200000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }) 2 ≤ ((335241 / 200000)+1*((1920157 / 2500000000)+(8962451 / 10000000000)+((8222903 / 2500000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)^2+2*(1*((1920157 / 2500000000)+(8962451 / 10000000000)+((8222903 / 2500000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)+(191 / 250)*((67647473 / 10000000000)+(5670363 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable22_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 ≤ ((-8416049 / 50000000) : ℝ) := by
    rw [concreteUnavailable22_value]
    have hp := concrete_poly_upper_bound (![(-21 / 40), (49 / 40), (-1 / 40), (-79 / 40), (-3 / 8), (119 / 40), (-15 / 8), (3 / 8)]) ((-8416049 / 50000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable22_L0, concreteUnavailable22_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((63991711 / 100000000) : ℝ) := by
    rw [concreteUnavailable22_A1]
    exact concrete_abs_poly036
  have hC : |dot (perp (cornerOffset constructionSquare 10 2)) (featureNormal constructionSquare ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable22_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 2, other := 10, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((-8416049 / 50000000)) (1) ((63991711 / 100000000)) ((5939131 / 100000000)) ((49095291 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable22_curvature ?_ h hh
  change (-8416049 / 50000000)+1*((1920157 / 2500000000)+(8962451 / 10000000000)+((8222903 / 2500000000)+(5212397 / 5000000000)))+(5670363 / 2500000000)*(63991711 / 100000000)+((67647473 / 10000000000)+(5670363 / 2500000000))*(5939131 / 100000000)+(49095291 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
