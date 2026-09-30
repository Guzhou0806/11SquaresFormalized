import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable17
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly03
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable17_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ ((9239831 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((352301 / 200000) : ℝ) := by
    rw [concreteUnavailable17_A0, concreteUnavailable17_A1]
    exact (add_le_add concrete_abs_poly012 concrete_abs_poly020).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable17_L0, concreteUnavailable17_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 3) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 8 3)) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable17_C0, concreteUnavailable17_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((352301 / 200000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ ((352301 / 200000)+1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)^2+2*(1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)+(191 / 250)*((7549783 / 5000000000)+(5670363 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable17_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 ≤ ((-35551073 / 20000000) : ℝ) := by
    rw [concreteUnavailable17_value]
    have hp := concrete_poly_upper_bound (![(-149 / 100), (-66 / 25), (491 / 100), (239 / 100), (-101 / 20), (-51 / 25), (15 / 4), (-23 / 20)]) ((-35551073 / 20000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable17_L0, concreteUnavailable17_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((118855871 / 100000000) : ℝ) := by
    rw [concreteUnavailable17_A1]
    exact concrete_abs_poly020
  have hC : |dot (perp (cornerOffset constructionSquare 8 3)) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable17_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((-35551073 / 20000000)) (1) ((118855871 / 100000000)) ((5939131 / 100000000)) ((9239831 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable17_curvature ?_ h hh
  change (-35551073 / 20000000)+1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000)))+(5670363 / 2500000000)*(118855871 / 100000000)+((7549783 / 5000000000)+(5670363 / 2500000000))*(5939131 / 100000000)+(9239831 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
