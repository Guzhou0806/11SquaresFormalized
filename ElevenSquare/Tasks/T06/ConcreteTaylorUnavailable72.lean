import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable72
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable72_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((106371291 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteUnavailable72_A0, concreteUnavailable72_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly071).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable72_L0, concreteUnavailable72_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 1) (featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 9 1)) (featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable72_C0, concreteUnavailable72_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((293551 / 400000000)+(11182451 / 10000000000)+((10335557 / 10000000000)+(3232837 / 5000000000))))*(8824483 / 2500000000)^2+2*((1409217 / 1000000)*((293551 / 400000000)+(11182451 / 10000000000)+((10335557 / 10000000000)+(3232837 / 5000000000))))*(8824483 / 2500000000)+1*((40352153 / 10000000000)+(8824483 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable72_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ (-2 : ℝ) := by
    rw [concreteUnavailable72_value]
    have hp := concrete_poly_upper_bound (![-2, 0, 0, 0, 0, 0, 0, 0]) (-2)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable72_L0, concreteUnavailable72_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((11878261 / 100000000) : ℝ) := by
    rw [concreteUnavailable72_A1]
    exact concrete_abs_poly071
  have hC : |dot (perp (cornerOffset constructionSquare 9 1)) (featureNormal constructionSquare ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable72_C1]
    exact concrete_abs_poly058
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1
    (-2) ((1409217 / 1000000)) ((11878261 / 100000000)) ((1 / 2)) ((106371291 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable72_curvature ?_ h hh
  change -2+(1409217 / 1000000)*((293551 / 400000000)+(11182451 / 10000000000)+((10335557 / 10000000000)+(3232837 / 5000000000)))+(8824483 / 2500000000)*(11878261 / 100000000)+((40352153 / 10000000000)+(8824483 / 2500000000))*(1 / 2)+(106371291 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
