import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable59
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable59_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) ≤ ((6373831 / 62500000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((8199 / 8000) : ℝ) := by
    rw [concreteUnavailable59_A0, concreteUnavailable59_A1]
    exact (add_le_add concrete_abs_poly024 concrete_abs_poly003).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable59_L0, concreteUnavailable59_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 7 2) (featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 7 2)) (featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable59_C0, concreteUnavailable59_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2
    ((8199 / 8000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2 ≤ ((8199 / 8000)+(1409217 / 1000000)*((11182451 / 10000000000)+(678279 / 500000000)+((3232837 / 5000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((11182451 / 10000000000)+(678279 / 500000000)+((3232837 / 5000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+1*((8824483 / 2500000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable59_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 ≤ ((-102487453 / 100000000) : ℝ) := by
    rw [concreteUnavailable59_value]
    have hp := concrete_poly_upper_bound (![(-9 / 10), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)]) ((-102487453 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable59_L0, concreteUnavailable59_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable59_A1]
    exact concrete_abs_poly003
  have hC : |dot (perp (cornerOffset constructionSquare 7 2)) (featureNormal constructionSquare ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable59_C1]
    exact concrete_abs_poly009
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 2
    ((-102487453 / 100000000)) ((1409217 / 1000000)) (1) ((1 / 2)) ((6373831 / 62500000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable59_curvature ?_ h hh
  change (-102487453 / 100000000)+(1409217 / 1000000)*((11182451 / 10000000000)+(678279 / 500000000)+((3232837 / 5000000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*1+((8824483 / 2500000000)+(35312013 / 10000000000))*(1 / 2)+(6373831 / 62500000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
