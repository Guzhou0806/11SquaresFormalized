import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable30
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable30_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }) 2) ≤ ((16045029 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable30_A0, concreteUnavailable30_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable30_L0, concreteUnavailable30_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 4 2) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 4 2)) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable30_C0, concreteUnavailable30_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }) 2
    (1) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }) 2 ≤ (1+1*((4087019 / 2500000000)+(1635053 / 1000000000)+((13962901 / 10000000000)+(10683139 / 10000000000))))*(1890121 / 1250000000)^2+2*(1*((4087019 / 2500000000)+(1635053 / 1000000000)+((13962901 / 10000000000)+(10683139 / 10000000000))))*(1890121 / 1250000000)+1*((20161291 / 10000000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable30_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 ≤ (-2 : ℝ) := by
    rw [concreteUnavailable30_value]
    have hp := concrete_poly_upper_bound (![-2, 0, 0, 0, 0, 0, 0, 0]) (-2)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable30_L0, concreteUnavailable30_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true })))| ≤ (0 : ℝ) := by
    rw [concreteUnavailable30_A1]
    exact concrete_abs_poly032
  have hC : |dot (perp (cornerOffset constructionSquare 4 2)) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable30_C1]
    exact concrete_abs_poly009
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := true }) 2
    (-2) (1) (0) ((1 / 2)) ((16045029 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable30_curvature ?_ h hh
  change -2+1*((4087019 / 2500000000)+(1635053 / 1000000000)+((13962901 / 10000000000)+(10683139 / 10000000000)))+(1890121 / 1250000000)*0+((20161291 / 10000000000)+(1890121 / 1250000000))*(1 / 2)+(16045029 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
