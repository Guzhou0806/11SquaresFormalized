import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable56
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable56_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 0) ≤ ((19948937 / 250000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((605563 / 500000) : ℝ) := by
    rw [concreteUnavailable56_A0, concreteUnavailable56_A1]
    exact (add_le_add concrete_abs_poly035 concrete_abs_poly075).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable56_L0, concreteUnavailable56_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 5 0) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 5 0)) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable56_C0, concreteUnavailable56_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 0
    ((605563 / 500000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 0 ≤ ((605563 / 500000)+(1409217 / 1000000)*((12900283 / 10000000000)+(678279 / 500000000)+((534153 / 500000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((12900283 / 10000000000)+(678279 / 500000000)+((534153 / 500000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+(191 / 250)*((1890121 / 1250000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable56_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 0) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 0) 0 ≤ ((-59904517 / 50000000) : ℝ) := by
    rw [concreteUnavailable56_value]
    have hp := concrete_poly_upper_bound (![-1, (-5 / 2), (29 / 4), (-5 / 2), (-15 / 2), (-3 / 2), (25 / 4), (-5 / 2)]) ((-59904517 / 50000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteUnavailable56_L0, concreteUnavailable56_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((120460817 / 100000000) : ℝ) := by
    rw [concreteUnavailable56_A1]
    exact concrete_abs_poly075
  have hC : |dot (perp (cornerOffset constructionSquare 5 0)) (featureNormal constructionSquare ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable56_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 6, other := 5, distinct := by decide, perpendicular := false, reverse := false }) 0
    ((-59904517 / 50000000)) ((1409217 / 1000000)) ((120460817 / 100000000)) ((5939131 / 100000000)) ((19948937 / 250000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable56_curvature ?_ h hh
  change (-59904517 / 50000000)+(1409217 / 1000000)*((12900283 / 10000000000)+(678279 / 500000000)+((534153 / 500000000)+(4124329 / 5000000000)))+(35312013 / 10000000000)*(120460817 / 100000000)+((1890121 / 1250000000)+(35312013 / 10000000000))*(5939131 / 100000000)+(19948937 / 250000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
