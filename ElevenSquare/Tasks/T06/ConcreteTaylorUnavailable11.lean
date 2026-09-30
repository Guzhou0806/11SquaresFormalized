import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable11
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable11_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }) 1) ≤ ((100287661 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((1236001 / 1000000) : ℝ) := by
    rw [concreteUnavailable11_A0, concreteUnavailable11_A1]
    exact (add_le_add concrete_abs_poly001 concrete_abs_poly025).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable11_L0, concreteUnavailable11_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 1 1) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 1 1)) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable11_C0, concreteUnavailable11_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((1236001 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }) 1 ≤ ((1236001 / 1000000)+(1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+(191 / 250)*((1764113 / 1000000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable11_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 ≤ ((-240921633 / 100000000) : ℝ) := by
    rw [concreteUnavailable11_value]
    have hp := concrete_poly_upper_bound (![(-83 / 40), (-73 / 40), (87 / 40), (53 / 40), (-9 / 8), (-23 / 40), (5 / 8), (-1 / 8)]) ((-240921633 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable11_L0, concreteUnavailable11_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((784809 / 25000000) : ℝ) := by
    rw [concreteUnavailable11_A1]
    exact concrete_abs_poly025
  have hC : |dot (perp (cornerOffset constructionSquare 1 1)) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable11_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((-240921633 / 100000000)) ((1409217 / 1000000)) ((784809 / 25000000)) ((5939131 / 100000000)) ((100287661 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable11_curvature ?_ h hh
  change (-240921633 / 100000000)+(1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000)))+(40352153 / 10000000000)*(784809 / 25000000)+((1764113 / 1000000000)+(40352153 / 10000000000))*(5939131 / 100000000)+(100287661 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
