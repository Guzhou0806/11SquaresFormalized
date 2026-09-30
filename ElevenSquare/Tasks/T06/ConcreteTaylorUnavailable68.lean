import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable68
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

theorem concreteUnavailable68_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 1) ≤ ((22466301 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteUnavailable68_A0, concreteUnavailable68_A1]
    exact (add_le_add concrete_abs_poly004 concrete_abs_poly072).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable68_L0, concreteUnavailable68_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 6 1) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 6 1)) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable68_C0, concreteUnavailable68_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 1 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((678279 / 500000000)+(9356857 / 10000000000)+((4124329 / 5000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)^2+2*((1409217 / 1000000)*((678279 / 500000000)+(9356857 / 10000000000)+((4124329 / 5000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)+1*((35312013 / 10000000000)+(7549783 / 5000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable68_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 ≤ ((-5593913 / 5000000) : ℝ) := by
    rw [concreteUnavailable68_value]
    have hp := concrete_poly_upper_bound (![(-79 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)]) ((-5593913 / 5000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable68_L0, concreteUnavailable68_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable68_A1]
    exact concrete_abs_poly072
  have hC : |dot (perp (cornerOffset constructionSquare 6 1)) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable68_C1]
    exact concrete_abs_poly058
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 8, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((-5593913 / 5000000)) ((1409217 / 1000000)) (1) ((1 / 2)) ((22466301 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable68_curvature ?_ h hh
  change (-5593913 / 5000000)+(1409217 / 1000000)*((678279 / 500000000)+(9356857 / 10000000000)+((4124329 / 5000000000)+(8671199 / 10000000000)))+(7549783 / 5000000000)*1+((35312013 / 10000000000)+(7549783 / 5000000000))*(1 / 2)+(22466301 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
