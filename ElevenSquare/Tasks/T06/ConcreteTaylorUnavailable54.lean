import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable54
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly13
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable54_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ ((18525649 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((84839 / 50000) : ℝ) := by
    rw [concreteUnavailable54_A0, concreteUnavailable54_A1]
    exact (add_le_add concrete_abs_poly052 concrete_abs_poly021).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable54_L0, concreteUnavailable54_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 6 3) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 6 3)) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable54_C0, concreteUnavailable54_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((84839 / 50000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ ((84839 / 50000)+1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000))))*(1890121 / 1250000000)^2+2*(1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000))))*(1890121 / 1250000000)+(191 / 250)*((35312013 / 10000000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable54_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 ≤ ((-43235427 / 100000000) : ℝ) := by
    rw [concreteUnavailable54_value]
    have hp := concrete_poly_upper_bound (![(-127 / 200), (203 / 200), (-557 / 200), (497 / 200), (187 / 40), (233 / 200), (-35 / 8), (71 / 40)]) ((-43235427 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable54_L0, concreteUnavailable54_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((46226271 / 50000000) : ℝ) := by
    rw [concreteUnavailable54_A1]
    exact concrete_abs_poly021
  have hC : |dot (perp (cornerOffset constructionSquare 6 3)) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable54_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((-43235427 / 100000000)) (1) ((46226271 / 50000000)) ((5939131 / 100000000)) ((18525649 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable54_curvature ?_ h hh
  change (-43235427 / 100000000)+1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000)))+(1890121 / 1250000000)*(46226271 / 50000000)+((35312013 / 10000000000)+(1890121 / 1250000000))*(5939131 / 100000000)+(18525649 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
