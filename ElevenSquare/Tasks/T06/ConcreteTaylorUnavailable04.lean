import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable04
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable04_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }) 3) ≤ ((13268419 / 125000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((1434091 / 1000000) : ℝ) := by
    rw [concreteUnavailable04_A0, concreteUnavailable04_A1]
    exact (add_le_add concrete_abs_poly039 concrete_abs_poly075).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable04_L0, concreteUnavailable04_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 0 3) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 0 3)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable04_C0, concreteUnavailable04_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((1434091 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }) 3 ≤ ((1434091 / 1000000)+(1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+(191 / 250)*((5670363 / 2500000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable04_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 ≤ ((-48756273 / 50000000) : ℝ) := by
    rw [concreteUnavailable04_value]
    have hp := concrete_poly_upper_bound (![(-11 / 10), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)]) ((-48756273 / 50000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable04_L0, concreteUnavailable04_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((120460817 / 100000000) : ℝ) := by
    rw [concreteUnavailable04_A1]
    exact concrete_abs_poly075
  have hC : |dot (perp (cornerOffset constructionSquare 0 3)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable04_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((-48756273 / 50000000)) ((1409217 / 1000000)) ((120460817 / 100000000)) ((5939131 / 100000000)) ((13268419 / 125000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable04_curvature ?_ h hh
  change (-48756273 / 50000000)+(1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*(120460817 / 100000000)+((5670363 / 2500000000)+(35312013 / 10000000000))*(5939131 / 100000000)+(13268419 / 125000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
