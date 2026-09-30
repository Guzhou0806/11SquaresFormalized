import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable27
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly11
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable27_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }) 2) ≤ ((12019627 / 50000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((692171 / 500000) : ℝ) := by
    rw [concreteUnavailable27_A0, concreteUnavailable27_A1]
    exact (add_le_add concrete_abs_poly046 concrete_abs_poly075).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable27_L0, concreteUnavailable27_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 2 2) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 2 2)) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable27_C0, concreteUnavailable27_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }) 2
    ((692171 / 500000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }) 2 ≤ ((692171 / 500000)+(1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)^2+2*((1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)+(191 / 250)*((5670363 / 2500000000)+(67647473 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable27_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }) 2) 0 ≤ ((-6921709 / 5000000) : ℝ) := by
    rw [concreteUnavailable27_value]
    have hp := concrete_poly_upper_bound (![(-47 / 40), (-21 / 20), (-37 / 40), (24 / 5), (31 / 8), (9 / 20), (-35 / 8), 2]) ((-6921709 / 5000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable27_L0, concreteUnavailable27_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((120460817 / 100000000) : ℝ) := by
    rw [concreteUnavailable27_A1]
    exact concrete_abs_poly075
  have hC : |dot (perp (cornerOffset constructionSquare 2 2)) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable27_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := false, reverse := true }) 2
    ((-6921709 / 5000000)) ((1409217 / 1000000)) ((120460817 / 100000000)) ((5939131 / 100000000)) ((12019627 / 50000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable27_curvature ?_ h hh
  change (-6921709 / 5000000)+(1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000)))+(67647473 / 10000000000)*(120460817 / 100000000)+((5670363 / 2500000000)+(67647473 / 10000000000))*(5939131 / 100000000)+(12019627 / 50000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
