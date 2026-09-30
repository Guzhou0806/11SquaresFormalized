import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable15
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly13
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable15_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 2) ≤ ((9239831 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((352301 / 200000) : ℝ) := by
    rw [concreteUnavailable15_A0, concreteUnavailable15_A1]
    exact (add_le_add concrete_abs_poly020 concrete_abs_poly055).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable15_L0, concreteUnavailable15_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 2) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 8 2)) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable15_C0, concreteUnavailable15_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((352301 / 200000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 2 ≤ ((352301 / 200000)+1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)^2+2*(1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)+(191 / 250)*((7549783 / 5000000000)+(5670363 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable15_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 ≤ ((-802473 / 50000000) : ℝ) := by
    rw [concreteUnavailable15_value]
    have hp := concrete_poly_upper_bound (![(-149 / 200), (311 / 200), (191 / 200), (89 / 200), (9 / 40), (321 / 200), (-15 / 8), (27 / 40)]) ((-802473 / 50000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable15_L0, concreteUnavailable15_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((57294549 / 100000000) : ℝ) := by
    rw [concreteUnavailable15_A1]
    exact concrete_abs_poly055
  have hC : |dot (perp (cornerOffset constructionSquare 8 2)) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable15_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((-802473 / 50000000)) (1) ((57294549 / 100000000)) ((5939131 / 100000000)) ((9239831 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable15_curvature ?_ h hh
  change (-802473 / 50000000)+1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000)))+(5670363 / 2500000000)*(57294549 / 100000000)+((7549783 / 5000000000)+(5670363 / 2500000000))*(5939131 / 100000000)+(9239831 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
