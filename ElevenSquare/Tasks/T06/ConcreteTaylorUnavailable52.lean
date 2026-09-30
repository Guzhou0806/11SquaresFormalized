import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable52
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly04
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable52_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }) 2) ≤ ((18525649 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((84839 / 50000) : ℝ) := by
    rw [concreteUnavailable52_A0, concreteUnavailable52_A1]
    exact (add_le_add concrete_abs_poly021 concrete_abs_poly016).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable52_L0, concreteUnavailable52_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 6 2) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 6 2)) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable52_C0, concreteUnavailable52_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((84839 / 50000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }) 2 ≤ ((84839 / 50000)+1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000))))*(1890121 / 1250000000)^2+2*(1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000))))*(1890121 / 1250000000)+(191 / 250)*((35312013 / 10000000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable52_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 ≤ ((-1120331 / 4000000) : ℝ) := by
    rw [concreteUnavailable52_value]
    have hp := concrete_poly_upper_bound (![(-171 / 200), (269 / 200), (-361 / 200), (981 / 200), (211 / 40), (-41 / 200), (-35 / 8), (83 / 40)]) ((-1120331 / 4000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable52_L0, concreteUnavailable52_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((7722539 / 10000000) : ℝ) := by
    rw [concreteUnavailable52_A1]
    exact concrete_abs_poly016
  have hC : |dot (perp (cornerOffset constructionSquare 6 2)) (featureNormal constructionSquare ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable52_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 5, other := 6, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((-1120331 / 4000000)) (1) ((7722539 / 10000000)) ((5939131 / 100000000)) ((18525649 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable52_curvature ?_ h hh
  change (-1120331 / 4000000)+1*((678279 / 500000000)+(12900283 / 10000000000)+((4124329 / 5000000000)+(534153 / 500000000)))+(1890121 / 1250000000)*(7722539 / 10000000)+((35312013 / 10000000000)+(1890121 / 1250000000))*(5939131 / 100000000)+(18525649 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
