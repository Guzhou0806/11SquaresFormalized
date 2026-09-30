import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable44
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable44_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0) ≤ ((35709673 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((412043 / 250000) : ℝ) := by
    rw [concreteUnavailable44_A0, concreteUnavailable44_A1]
    exact (add_le_add concrete_abs_poly020 concrete_abs_poly027).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable44_L0, concreteUnavailable44_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 0) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 8 0)) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable44_C0, concreteUnavailable44_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((412043 / 250000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0 ≤ ((412043 / 250000)+1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)^2+2*(1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)+(191 / 250)*((7549783 / 5000000000)+(20161291 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable44_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 ≤ ((-239316687 / 100000000) : ℝ) := by
    rw [concreteUnavailable44_value]
    have hp := concrete_poly_upper_bound (![(-133 / 100), (-169 / 50), (61 / 50), (22 / 25), (-27 / 20), (-109 / 50), (5 / 2), (-4 / 5)]) ((-239316687 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable44_L0, concreteUnavailable44_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((45961283 / 100000000) : ℝ) := by
    rw [concreteUnavailable44_A1]
    exact concrete_abs_poly027
  have hC : |dot (perp (cornerOffset constructionSquare 8 0)) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable44_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((-239316687 / 100000000)) (1) ((45961283 / 100000000)) ((5939131 / 100000000)) ((35709673 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable44_curvature ?_ h hh
  change (-239316687 / 100000000)+1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000)))+(20161291 / 10000000000)*(45961283 / 100000000)+((7549783 / 5000000000)+(20161291 / 10000000000))*(5939131 / 100000000)+(35709673 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
