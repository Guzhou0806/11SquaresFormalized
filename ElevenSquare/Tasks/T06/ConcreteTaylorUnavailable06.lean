import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable06
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable06_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }) 0) ≤ ((13268419 / 125000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((1434091 / 1000000) : ℝ) := by
    rw [concreteUnavailable06_A0, concreteUnavailable06_A1]
    exact (add_le_add concrete_abs_poly001 concrete_abs_poly039).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable06_L0, concreteUnavailable06_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 0 0) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 0 0)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable06_C0, concreteUnavailable06_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }) 0
    ((1434091 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }) 0 ≤ ((1434091 / 1000000)+(1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+(191 / 250)*((5670363 / 2500000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable06_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }) 0) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 ≤ ((-240921633 / 100000000) : ℝ) := by
    rw [concreteUnavailable06_value]
    have hp := concrete_poly_upper_bound (![(-83 / 40), (-73 / 40), (87 / 40), (53 / 40), (-9 / 8), (-23 / 40), (5 / 8), (-1 / 8)]) ((-240921633 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable06_L0, concreteUnavailable06_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((22948271 / 100000000) : ℝ) := by
    rw [concreteUnavailable06_A1]
    exact concrete_abs_poly039
  have hC : |dot (perp (cornerOffset constructionSquare 0 0)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable06_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := false }) 0
    ((-240921633 / 100000000)) ((1409217 / 1000000)) ((22948271 / 100000000)) ((5939131 / 100000000)) ((13268419 / 125000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable06_curvature ?_ h hh
  change (-240921633 / 100000000)+(1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*(22948271 / 100000000)+((5670363 / 2500000000)+(35312013 / 10000000000))*(5939131 / 100000000)+(13268419 / 125000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
