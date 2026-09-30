import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable07
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly12
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable07_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }) 0) ≤ ((47844391 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((67753 / 40000) : ℝ) := by
    rw [concreteUnavailable07_A0, concreteUnavailable07_A1]
    exact (add_le_add concrete_abs_poly069 concrete_abs_poly051).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable07_L0, concreteUnavailable07_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 0) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 9 0)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable07_C0, concreteUnavailable07_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((67753 / 40000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }) 0 ≤ ((67753 / 40000)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)^2+2*(1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)+(191 / 250)*((40352153 / 10000000000)+(1764113 / 1000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable07_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }) 0) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 ≤ ((-103138 / 390625) : ℝ) := by
    rw [concreteUnavailable07_value]
    have hp := concrete_poly_upper_bound (![(-11 / 100), (-21 / 100), (-69 / 25), (223 / 50), (101 / 20), (-181 / 100), (-5 / 2), (7 / 5)]) ((-103138 / 390625))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable07_L0, concreteUnavailable07_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((75324977 / 100000000) : ℝ) := by
    rw [concreteUnavailable07_A1]
    exact concrete_abs_poly051
  have hC : |dot (perp (cornerOffset constructionSquare 9 0)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable07_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((-103138 / 390625)) (1) ((75324977 / 100000000)) ((5939131 / 100000000)) ((47844391 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable07_curvature ?_ h hh
  change (-103138 / 390625)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000)))+(1764113 / 1000000000)*(75324977 / 100000000)+((40352153 / 10000000000)+(1764113 / 1000000000))*(5939131 / 100000000)+(47844391 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
