import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable47
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable47_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ ((35709673 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((412043 / 250000) : ℝ) := by
    rw [concreteUnavailable47_A0, concreteUnavailable47_A1]
    exact (add_le_add concrete_abs_poly037 concrete_abs_poly020).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable47_L0, concreteUnavailable47_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 3) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 8 3)) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable47_C0, concreteUnavailable47_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((412043 / 250000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ ((412043 / 250000)+1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)^2+2*(1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)+(191 / 250)*((7549783 / 5000000000)+(20161291 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable47_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 ≤ ((-37249767 / 50000000) : ℝ) := by
    rw [concreteUnavailable47_value]
    have hp := concrete_poly_upper_bound (![(-99 / 100), (-7 / 50), (4 / 25), (489 / 100), (49 / 20), (-27 / 50), (-5 / 2), (27 / 20)]) ((-37249767 / 50000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable47_L0, concreteUnavailable47_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((118855871 / 100000000) : ℝ) := by
    rw [concreteUnavailable47_A1]
    exact concrete_abs_poly020
  have hC : |dot (perp (cornerOffset constructionSquare 8 3)) (featureNormal constructionSquare ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable47_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 4, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((-37249767 / 50000000)) (1) ((118855871 / 100000000)) ((5939131 / 100000000)) ((35709673 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable47_curvature ?_ h hh
  change (-37249767 / 50000000)+1*((9356857 / 10000000000)+(4087019 / 2500000000)+((8671199 / 10000000000)+(13962901 / 10000000000)))+(20161291 / 10000000000)*(118855871 / 100000000)+((7549783 / 5000000000)+(20161291 / 10000000000))*(5939131 / 100000000)+(35709673 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
