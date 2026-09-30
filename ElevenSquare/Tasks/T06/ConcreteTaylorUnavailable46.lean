import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable46
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable46_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((35709673 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((412043 / 250000) : ℝ) := by
    rw [concreteUnavailable46_A0, concreteUnavailable46_A1]
    exact (add_le_add concrete_abs_poly037 concrete_abs_poly020).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable46_L0, concreteUnavailable46_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 1) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 8 1)) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable46_C0, concreteUnavailable46_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((412043 / 250000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((412043 / 250000)+1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)^2+2*(1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)+(191 / 250)*((7549783 / 5000000000)+(20161291 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable46_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ ((-166422099 / 100000000) : ℝ) := by
    rw [concreteUnavailable46_value]
    have hp := concrete_poly_upper_bound (![(-217 / 200), (-337 / 200), (403 / 200), (-713 / 200), (-143 / 40), (-7 / 200), (25 / 8), (-59 / 40)]) ((-166422099 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable46_L0, concreteUnavailable46_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((118855871 / 100000000) : ℝ) := by
    rw [concreteUnavailable46_A1]
    exact concrete_abs_poly020
  have hC : |dot (perp (cornerOffset constructionSquare 8 1)) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable46_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((-166422099 / 100000000)) (1) ((118855871 / 100000000)) ((5939131 / 100000000)) ((35709673 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable46_curvature ?_ h hh
  change (-166422099 / 100000000)+1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000)))+(20161291 / 10000000000)*(118855871 / 100000000)+((7549783 / 5000000000)+(20161291 / 10000000000))*(5939131 / 100000000)+(35709673 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
