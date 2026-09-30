import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable55
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly07
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable55_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) ≤ ((19948937 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((605563 / 500000) : ℝ) := by
    rw [concreteUnavailable55_A0, concreteUnavailable55_A1]
    exact (add_le_add concrete_abs_poly075 concrete_abs_poly029).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable55_L0, concreteUnavailable55_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 5 3) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 5 3)) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable55_C0, concreteUnavailable55_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((605563 / 500000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 ≤ ((605563 / 500000)+(1409217 / 1000000)*((12900283 / 10000000000)+(678279 / 500000000)+((534153 / 500000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((12900283 / 10000000000)+(678279 / 500000000)+((534153 / 500000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+(191 / 250)*((1890121 / 1250000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable55_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 ≤ ((-240921633 / 100000000) : ℝ) := by
    rw [concreteUnavailable55_value]
    have hp := concrete_poly_upper_bound (![(-83 / 40), (-73 / 40), (87 / 40), (53 / 40), (-9 / 8), (-23 / 40), (5 / 8), (-1 / 8)]) ((-240921633 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable55_L0, concreteUnavailable55_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((651783 / 100000000) : ℝ) := by
    rw [concreteUnavailable55_A1]
    exact concrete_abs_poly029
  have hC : |dot (perp (cornerOffset constructionSquare 5 3)) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable55_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((-240921633 / 100000000)) ((1409217 / 1000000)) ((651783 / 100000000)) ((5939131 / 100000000)) ((19948937 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable55_curvature ?_ h hh
  change (-240921633 / 100000000)+(1409217 / 1000000)*((12900283 / 10000000000)+(678279 / 500000000)+((534153 / 500000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*(651783 / 100000000)+((1890121 / 1250000000)+(35312013 / 10000000000))*(5939131 / 100000000)+(19948937 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
