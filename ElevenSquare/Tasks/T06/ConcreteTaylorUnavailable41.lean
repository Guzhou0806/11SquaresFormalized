import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable41
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable41_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ ((2116571 / 50000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })))| ≤ (2 : ℝ) := by
    rw [concreteUnavailable41_A0, concreteUnavailable41_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly003).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable41_L0, concreteUnavailable41_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 5 3) (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 5 3)) (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable41_C0, concreteUnavailable41_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 3
    (2) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ (2+1*((12900283 / 10000000000)+(4087019 / 2500000000)+((534153 / 500000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)^2+2*(1*((12900283 / 10000000000)+(4087019 / 2500000000)+((534153 / 500000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)+1*((1890121 / 1250000000)+(20161291 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable41_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 ≤ (-2 : ℝ) := by
    rw [concreteUnavailable41_value]
    have hp := concrete_poly_upper_bound (![-2, 0, 0, 0, 0, 0, 0, 0]) (-2)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable41_L0, concreteUnavailable41_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable41_A1]
    exact concrete_abs_poly003
  have hC : |dot (perp (cornerOffset constructionSquare 5 3)) (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable41_C1]
    exact concrete_abs_poly009
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 3
    (-2) (1) (1) ((1 / 2)) ((2116571 / 50000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable41_curvature ?_ h hh
  change -2+1*((12900283 / 10000000000)+(4087019 / 2500000000)+((534153 / 500000000)+(13962901 / 10000000000)))+(20161291 / 10000000000)*1+((1890121 / 1250000000)+(20161291 / 10000000000))*(1 / 2)+(2116571 / 50000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
