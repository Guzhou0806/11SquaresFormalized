import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable05
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable05_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }) 1) ≤ ((13268419 / 125000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((1434091 / 1000000) : ℝ) := by
    rw [concreteUnavailable05_A0, concreteUnavailable05_A1]
    exact (add_le_add concrete_abs_poly039 concrete_abs_poly075).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable05_L0, concreteUnavailable05_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 0 1) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 0 1)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable05_C0, concreteUnavailable05_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((1434091 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }) 1 ≤ ((1434091 / 1000000)+(1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+(191 / 250)*((5670363 / 2500000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable05_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }) 1) 0 ≤ ((-143409087 / 100000000) : ℝ) := by
    rw [concreteUnavailable05_value]
    have hp := concrete_poly_upper_bound (![(-39 / 40), (-13 / 5), (211 / 40), (-43 / 20), (-49 / 8), (-8 / 5), (45 / 8), (-9 / 4)]) ((-143409087 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable05_L0, concreteUnavailable05_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((120460817 / 100000000) : ℝ) := by
    rw [concreteUnavailable05_A1]
    exact concrete_abs_poly075
  have hC : |dot (perp (cornerOffset constructionSquare 0 1)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable05_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((-143409087 / 100000000)) ((1409217 / 1000000)) ((120460817 / 100000000)) ((5939131 / 100000000)) ((13268419 / 125000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable05_curvature ?_ h hh
  change (-143409087 / 100000000)+(1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*(120460817 / 100000000)+((5670363 / 2500000000)+(35312013 / 10000000000))*(5939131 / 100000000)+(13268419 / 125000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
