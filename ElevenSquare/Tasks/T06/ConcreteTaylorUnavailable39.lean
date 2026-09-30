import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable39
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable39_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((13375661 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable39_A0, concreteUnavailable39_A1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable39_L0, concreteUnavailable39_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 3 1) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 3 1)) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable39_C0, concreteUnavailable39_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1
    (1) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ (1+1*((1635053 / 1000000000)+(12900283 / 10000000000)+((10683139 / 10000000000)+(534153 / 500000000))))*(1890121 / 1250000000)^2+2*(1*((1635053 / 1000000000)+(12900283 / 10000000000)+((10683139 / 10000000000)+(534153 / 500000000))))*(1890121 / 1250000000)+1*((1890121 / 1250000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable39_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ (-1 : ℝ) := by
    rw [concreteUnavailable39_value]
    have hp := concrete_poly_upper_bound (![-1, 0, 0, 0, 0, 0, 0, 0]) (-1)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable39_L0, concreteUnavailable39_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable39_A1]
    exact concrete_abs_poly072
  have hC : |dot (perp (cornerOffset constructionSquare 3 1)) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable39_C1]
    exact concrete_abs_poly058
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 5, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1
    (-1) (1) (1) ((1 / 2)) ((13375661 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable39_curvature ?_ h hh
  change -1+1*((1635053 / 1000000000)+(12900283 / 10000000000)+((10683139 / 10000000000)+(534153 / 500000000)))+(1890121 / 1250000000)*1+((1890121 / 1250000000)+(1890121 / 1250000000))*(1 / 2)+(13375661 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
