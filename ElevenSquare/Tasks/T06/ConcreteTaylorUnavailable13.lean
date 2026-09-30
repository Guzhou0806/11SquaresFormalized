import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable13
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly10
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable13_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }) 2) ≤ ((100287661 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((1236001 / 1000000) : ℝ) := by
    rw [concreteUnavailable13_A0, concreteUnavailable13_A1]
    exact (add_le_add concrete_abs_poly040 concrete_abs_poly001).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable13_L0, concreteUnavailable13_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 1 2) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 1 2)) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable13_C0, concreteUnavailable13_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }) 2
    ((1236001 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }) 2 ≤ ((1236001 / 1000000)+(1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+(191 / 250)*((1764113 / 1000000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable13_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 ≤ ((-117321581 / 100000000) : ℝ) := by
    rw [concreteUnavailable13_value]
    have hp := concrete_poly_upper_bound (![(-11 / 10), (-69 / 40), (83 / 20), (39 / 40), (-5 / 2), (-19 / 40), (5 / 4), (-3 / 8)]) ((-117321581 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable13_L0, concreteUnavailable13_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((120460817 / 100000000) : ℝ) := by
    rw [concreteUnavailable13_A1]
    exact concrete_abs_poly001
  have hC : |dot (perp (cornerOffset constructionSquare 1 2)) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable13_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := false, reverse := true }) 2
    ((-117321581 / 100000000)) ((1409217 / 1000000)) ((120460817 / 100000000)) ((5939131 / 100000000)) ((100287661 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable13_curvature ?_ h hh
  change (-117321581 / 100000000)+(1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000)))+(40352153 / 10000000000)*(120460817 / 100000000)+((1764113 / 1000000000)+(40352153 / 10000000000))*(5939131 / 100000000)+(100287661 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
