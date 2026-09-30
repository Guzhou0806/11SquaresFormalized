import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable53
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly13
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable53_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((18525649 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((84839 / 50000) : ℝ) := by
    rw [concreteUnavailable53_A0, concreteUnavailable53_A1]
    exact (add_le_add concrete_abs_poly052 concrete_abs_poly021).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable53_L0, concreteUnavailable53_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 6 1) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 6 1)) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable53_C0, concreteUnavailable53_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((84839 / 50000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((84839 / 50000)+1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000))))*(1890121 / 1250000000)^2+2*(1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000))))*(1890121 / 1250000000)+(191 / 250)*((35312013 / 10000000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable53_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ ((-98843103 / 50000000) : ℝ) := by
    rw [concreteUnavailable53_value]
    have hp := concrete_poly_upper_bound (![(-36 / 25), (-71 / 25), (124 / 25), (-29 / 25), (-29 / 5), (-87 / 50), 5, (-19 / 10)]) ((-98843103 / 50000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable53_L0, concreteUnavailable53_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((46226271 / 50000000) : ℝ) := by
    rw [concreteUnavailable53_A1]
    exact concrete_abs_poly021
  have hC : |dot (perp (cornerOffset constructionSquare 6 1)) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable53_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((-98843103 / 50000000)) (1) ((46226271 / 50000000)) ((5939131 / 100000000)) ((18525649 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable53_curvature ?_ h hh
  change (-98843103 / 50000000)+1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000)))+(1890121 / 1250000000)*(46226271 / 50000000)+((35312013 / 10000000000)+(1890121 / 1250000000))*(5939131 / 100000000)+(18525649 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
