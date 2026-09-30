import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable33
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable33_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ ((19829653 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable33_A0, concreteUnavailable33_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly032).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable33_L0, concreteUnavailable33_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 3 3) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 3 3)) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable33_C0, concreteUnavailable33_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 3
    (1) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ (1+1*((1635053 / 1000000000)+(4087019 / 2500000000)+((10683139 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)^2+2*(1*((1635053 / 1000000000)+(4087019 / 2500000000)+((10683139 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)+1*((1890121 / 1250000000)+(20161291 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable33_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 ≤ (-2 : ℝ) := by
    rw [concreteUnavailable33_value]
    have hp := concrete_poly_upper_bound (![-2, 0, 0, 0, 0, 0, 0, 0]) (-2)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable33_L0, concreteUnavailable33_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false })))| ≤ (0 : ℝ) := by
    rw [concreteUnavailable33_A1]
    exact concrete_abs_poly032
  have hC : |dot (perp (cornerOffset constructionSquare 3 3)) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable33_C1]
    exact concrete_abs_poly009
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := false }) 3
    (-2) (1) (0) ((1 / 2)) ((19829653 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable33_curvature ?_ h hh
  change -2+1*((1635053 / 1000000000)+(4087019 / 2500000000)+((10683139 / 10000000000)+(13962901 / 10000000000)))+(20161291 / 10000000000)*0+((1890121 / 1250000000)+(20161291 / 10000000000))*(1 / 2)+(19829653 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
