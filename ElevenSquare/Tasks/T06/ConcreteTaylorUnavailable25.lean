import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable25
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable25_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }) 3) ≤ ((12019627 / 50000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((692171 / 500000) : ℝ) := by
    rw [concreteUnavailable25_A0, concreteUnavailable25_A1]
    exact (add_le_add concrete_abs_poly075 concrete_abs_poly022).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable25_L0, concreteUnavailable25_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 2 3) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 2 3)) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable25_C0, concreteUnavailable25_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((692171 / 500000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }) 3 ≤ ((692171 / 500000)+(1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)^2+2*((1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)+(191 / 250)*((5670363 / 2500000000)+(67647473 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable25_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }) 3) 0 ≤ ((-240921633 / 100000000) : ℝ) := by
    rw [concreteUnavailable25_value]
    have hp := concrete_poly_upper_bound (![(-83 / 40), (-73 / 40), (87 / 40), (53 / 40), (-9 / 8), (-23 / 40), (5 / 8), (-1 / 8)]) ((-240921633 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable25_L0, concreteUnavailable25_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((4493341 / 25000000) : ℝ) := by
    rw [concreteUnavailable25_A1]
    exact concrete_abs_poly022
  have hC : |dot (perp (cornerOffset constructionSquare 2 3)) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable25_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((-240921633 / 100000000)) ((1409217 / 1000000)) ((4493341 / 25000000)) ((5939131 / 100000000)) ((12019627 / 50000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable25_curvature ?_ h hh
  change (-240921633 / 100000000)+(1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000)))+(67647473 / 10000000000)*(4493341 / 25000000)+((5670363 / 2500000000)+(67647473 / 10000000000))*(5939131 / 100000000)+(12019627 / 50000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
