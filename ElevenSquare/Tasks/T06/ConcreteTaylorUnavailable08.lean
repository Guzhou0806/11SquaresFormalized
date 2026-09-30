import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable08
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly12
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable08_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) ≤ ((47844391 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((67753 / 40000) : ℝ) := by
    rw [concreteUnavailable08_A0, concreteUnavailable08_A1]
    exact (add_le_add concrete_abs_poly069 concrete_abs_poly051).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable08_L0, concreteUnavailable08_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 2) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 9 2)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable08_C0, concreteUnavailable08_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((67753 / 40000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 ≤ ((67753 / 40000)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)^2+2*(1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)+(191 / 250)*((40352153 / 10000000000)+(1764113 / 1000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable08_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) 0 ≤ ((-42903661 / 20000000) : ℝ) := by
    rw [concreteUnavailable08_value]
    have hp := concrete_poly_upper_bound (![(-393 / 200), (-323 / 200), (987 / 200), (-627 / 200), (-247 / 40), (247 / 200), (25 / 8), (-61 / 40)]) ((-42903661 / 20000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable08_L0, concreteUnavailable08_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((75324977 / 100000000) : ℝ) := by
    rw [concreteUnavailable08_A1]
    exact concrete_abs_poly051
  have hC : |dot (perp (cornerOffset constructionSquare 9 2)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable08_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((-42903661 / 20000000)) (1) ((75324977 / 100000000)) ((5939131 / 100000000)) ((47844391 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable08_curvature ?_ h hh
  change (-42903661 / 20000000)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000)))+(1764113 / 1000000000)*(75324977 / 100000000)+((40352153 / 10000000000)+(1764113 / 1000000000))*(5939131 / 100000000)+(47844391 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
