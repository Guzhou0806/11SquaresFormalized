import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable74
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable74_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }) 1) ≤ ((23139939 / 200000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteUnavailable74_A0, concreteUnavailable74_A1]
    exact (add_le_add concrete_abs_poly004 concrete_abs_poly072).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable74_L0, concreteUnavailable74_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 7 1) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 7 1)) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable74_C0, concreteUnavailable74_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }) 1 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((11182451 / 10000000000)+(293551 / 400000000)+((3232837 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((11182451 / 10000000000)+(293551 / 400000000)+((3232837 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+1*((8824483 / 2500000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable74_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 ≤ ((-5593913 / 5000000) : ℝ) := by
    rw [concreteUnavailable74_value]
    have hp := concrete_poly_upper_bound (![(-79 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)]) ((-5593913 / 5000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable74_L0, concreteUnavailable74_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable74_A1]
    exact concrete_abs_poly072
  have hC : |dot (perp (cornerOffset constructionSquare 7 1)) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable74_C1]
    exact concrete_abs_poly058
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 9, other := 7, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((-5593913 / 5000000)) ((1409217 / 1000000)) (1) ((1 / 2)) ((23139939 / 200000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable74_curvature ?_ h hh
  change (-5593913 / 5000000)+(1409217 / 1000000)*((11182451 / 10000000000)+(293551 / 400000000)+((3232837 / 5000000000)+(10335557 / 10000000000)))+(40352153 / 10000000000)*1+((8824483 / 2500000000)+(40352153 / 10000000000))*(1 / 2)+(23139939 / 200000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
