import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable69
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable69_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ ((22466301 / 500000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteUnavailable69_A0, concreteUnavailable69_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly004).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable69_L0, concreteUnavailable69_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 6 3) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 6 3)) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable69_C0, concreteUnavailable69_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((678279 / 500000000)+(9356857 / 10000000000)+((4124329 / 5000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)^2+2*((1409217 / 1000000)*((678279 / 500000000)+(9356857 / 10000000000)+((4124329 / 5000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)+1*((35312013 / 10000000000)+(7549783 / 5000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable69_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 ≤ (-2 : ℝ) := by
    rw [concreteUnavailable69_value]
    have hp := concrete_poly_upper_bound (![-2, 0, 0, 0, 0, 0, 0, 0]) (-2)
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable69_L0, concreteUnavailable69_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((11878261 / 100000000) : ℝ) := by
    rw [concreteUnavailable69_A1]
    exact concrete_abs_poly004
  have hC : |dot (perp (cornerOffset constructionSquare 6 3)) (featureNormal constructionSquare ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable69_C1]
    exact concrete_abs_poly009
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := false }) 3
    (-2) ((1409217 / 1000000)) ((11878261 / 100000000)) ((1 / 2)) ((22466301 / 500000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable69_curvature ?_ h hh
  change -2+(1409217 / 1000000)*((678279 / 500000000)+(9356857 / 10000000000)+((4124329 / 5000000000)+(8671199 / 10000000000)))+(7549783 / 5000000000)*(11878261 / 100000000)+((35312013 / 10000000000)+(7549783 / 5000000000))*(1 / 2)+(22466301 / 500000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
