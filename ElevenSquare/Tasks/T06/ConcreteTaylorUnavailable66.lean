import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable66
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable66_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((79086693 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteUnavailable66_A0, concreteUnavailable66_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly071).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable66_L0, concreteUnavailable66_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 1) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 8 1)) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable66_C0, concreteUnavailable66_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+1*((7549783 / 5000000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable66_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ (-2 : ℝ) := by
    rw [concreteUnavailable66_value]
    have hp := concrete_poly_upper_bound (![-2, 0, 0, 0, 0, 0, 0, 0]) (-2)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable66_L0, concreteUnavailable66_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((11878261 / 100000000) : ℝ) := by
    rw [concreteUnavailable66_A1]
    exact concrete_abs_poly071
  have hC : |dot (perp (cornerOffset constructionSquare 8 1)) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable66_C1]
    exact concrete_abs_poly058
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1
    (-2) ((1409217 / 1000000)) ((11878261 / 100000000)) ((1 / 2)) ((79086693 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable66_curvature ?_ h hh
  change -2+(1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*(11878261 / 100000000)+((7549783 / 5000000000)+(35312013 / 10000000000))*(1 / 2)+(79086693 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
