import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable48
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable48_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }) 3) ≤ ((6756119 / 200000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((1620343 / 1000000) : ℝ) := by
    rw [concreteUnavailable48_A0, concreteUnavailable48_A1]
    exact (add_le_add concrete_abs_poly075 concrete_abs_poly023).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable48_L0, concreteUnavailable48_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 4 3) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 4 3)) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable48_C0, concreteUnavailable48_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((1620343 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }) 3 ≤ ((1620343 / 1000000)+(1409217 / 1000000)*((4087019 / 2500000000)+(9356857 / 10000000000)+((13962901 / 10000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)^2+2*((1409217 / 1000000)*((4087019 / 2500000000)+(9356857 / 10000000000)+((13962901 / 10000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)+(191 / 250)*((20161291 / 10000000000)+(7549783 / 5000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable48_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 ≤ ((-240921633 / 100000000) : ℝ) := by
    rw [concreteUnavailable48_value]
    have hp := concrete_poly_upper_bound (![(-83 / 40), (-73 / 40), (87 / 40), (53 / 40), (-9 / 8), (-23 / 40), (5 / 8), (-1 / 8)]) ((-240921633 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable48_L0, concreteUnavailable48_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((41573417 / 100000000) : ℝ) := by
    rw [concreteUnavailable48_A1]
    exact concrete_abs_poly023
  have hC : |dot (perp (cornerOffset constructionSquare 4 3)) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable48_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((-240921633 / 100000000)) ((1409217 / 1000000)) ((41573417 / 100000000)) ((5939131 / 100000000)) ((6756119 / 200000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable48_curvature ?_ h hh
  change (-240921633 / 100000000)+(1409217 / 1000000)*((4087019 / 2500000000)+(9356857 / 10000000000)+((13962901 / 10000000000)+(8671199 / 10000000000)))+(7549783 / 5000000000)*(41573417 / 100000000)+((20161291 / 10000000000)+(7549783 / 5000000000))*(5939131 / 100000000)+(6756119 / 200000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
