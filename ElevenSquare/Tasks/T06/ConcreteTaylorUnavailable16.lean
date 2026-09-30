import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable16
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly03
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable16_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((9239831 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((352301 / 200000) : ℝ) := by
    rw [concreteUnavailable16_A0, concreteUnavailable16_A1]
    exact (add_le_add concrete_abs_poly012 concrete_abs_poly020).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable16_L0, concreteUnavailable16_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 1) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 8 1)) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable16_C0, concreteUnavailable16_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((352301 / 200000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((352301 / 200000)+1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)^2+2*(1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000))))*(5670363 / 2500000000)+(191 / 250)*((7549783 / 5000000000)+(5670363 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable16_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ ((-15791567 / 25000000) : ℝ) := by
    rw [concreteUnavailable16_value]
    have hp := concrete_poly_upper_bound (![(-117 / 200), (163 / 200), (-547 / 200), (-213 / 200), (157 / 40), (293 / 200), (-25 / 8), (41 / 40)]) ((-15791567 / 25000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable16_L0, concreteUnavailable16_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((118855871 / 100000000) : ℝ) := by
    rw [concreteUnavailable16_A1]
    exact concrete_abs_poly020
  have hC : |dot (perp (cornerOffset constructionSquare 8 1)) (featureNormal constructionSquare ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable16_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 2, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((-15791567 / 25000000)) (1) ((118855871 / 100000000)) ((5939131 / 100000000)) ((9239831 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable16_curvature ?_ h hh
  change (-15791567 / 25000000)+1*((9356857 / 10000000000)+(8962451 / 10000000000)+((8671199 / 10000000000)+(5212397 / 5000000000)))+(5670363 / 2500000000)*(118855871 / 100000000)+((7549783 / 5000000000)+(5670363 / 2500000000))*(5939131 / 100000000)+(9239831 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
