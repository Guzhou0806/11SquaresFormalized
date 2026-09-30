import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable09
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly04
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable09_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((47844391 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((67753 / 40000) : ℝ) := by
    rw [concreteUnavailable09_A0, concreteUnavailable09_A1]
    exact (add_le_add concrete_abs_poly018 concrete_abs_poly069).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable09_L0, concreteUnavailable09_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 1) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 9 1)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable09_C0, concreteUnavailable09_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((67753 / 40000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((67753 / 40000)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)^2+2*(1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)+(191 / 250)*((40352153 / 10000000000)+(1764113 / 1000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable09_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ ((-282099 / 625000) : ℝ) := by
    rw [concreteUnavailable09_value]
    have hp := concrete_poly_upper_bound (![(-67 / 100), (251 / 200), (-97 / 100), (-551 / 200), (17 / 20), (361 / 200), (-5 / 4), (7 / 40)]) ((-282099 / 625000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable09_L0, concreteUnavailable09_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((94057489 / 100000000) : ℝ) := by
    rw [concreteUnavailable09_A1]
    exact concrete_abs_poly069
  have hC : |dot (perp (cornerOffset constructionSquare 9 1)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable09_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((-282099 / 625000)) (1) ((94057489 / 100000000)) ((5939131 / 100000000)) ((47844391 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable09_curvature ?_ h hh
  change (-282099 / 625000)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000)))+(1764113 / 1000000000)*(94057489 / 100000000)+((40352153 / 10000000000)+(1764113 / 1000000000))*(5939131 / 100000000)+(47844391 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
