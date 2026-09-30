import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable65
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable65_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 3) ≤ ((79086693 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteUnavailable65_A0, concreteUnavailable65_A1]
    exact (add_le_add concrete_abs_poly071 concrete_abs_poly003).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable65_L0, concreteUnavailable65_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 3) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 8 3)) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable65_C0, concreteUnavailable65_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 3 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+1*((7549783 / 5000000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable65_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 ≤ ((-5593913 / 5000000) : ℝ) := by
    rw [concreteUnavailable65_value]
    have hp := concrete_poly_upper_bound (![(-79 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)]) ((-5593913 / 5000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable65_L0, concreteUnavailable65_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteUnavailable65_A1]
    exact concrete_abs_poly003
  have hC : |dot (perp (cornerOffset constructionSquare 8 3)) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((1 / 2) : ℝ) := by
    rw [concreteUnavailable65_C1]
    exact concrete_abs_poly009
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((-5593913 / 5000000)) ((1409217 / 1000000)) (1) ((1 / 2)) ((79086693 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable65_curvature ?_ h hh
  change (-5593913 / 5000000)+(1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*1+((7549783 / 5000000000)+(35312013 / 10000000000))*(1 / 2)+(79086693 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
