import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable10
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly04
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable10_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ ((47844391 / 1000000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((67753 / 40000) : ℝ) := by
    rw [concreteUnavailable10_A0, concreteUnavailable10_A1]
    exact (add_le_add concrete_abs_poly018 concrete_abs_poly069).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable10_L0, concreteUnavailable10_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 3) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 9 3)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable10_C0, concreteUnavailable10_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((67753 / 40000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ ((67753 / 40000)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)^2+2*(1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000))))*(1764113 / 1000000000)+(191 / 250)*((40352153 / 10000000000)+(1764113 / 1000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable10_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }) 3) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }) 3) 0 ≤ ((-195785793 / 100000000) : ℝ) := by
    rw [concreteUnavailable10_value]
    have hp := concrete_poly_upper_bound (![(-281 / 200), (-77 / 25), (629 / 200), (102 / 25), (-79 / 40), (-119 / 50), (15 / 8), (-3 / 10)]) ((-195785793 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable10_L0, concreteUnavailable10_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((94057489 / 100000000) : ℝ) := by
    rw [concreteUnavailable10_A1]
    exact concrete_abs_poly069
  have hC : |dot (perp (cornerOffset constructionSquare 9 3)) (featureNormal constructionSquare ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable10_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 1, other := 9, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((-195785793 / 100000000)) (1) ((94057489 / 100000000)) ((5939131 / 100000000)) ((47844391 / 1000000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable10_curvature ?_ h hh
  change (-195785793 / 100000000)+1*((293551 / 400000000)+(1636033 / 1000000000)+((10335557 / 10000000000)+(6880181 / 5000000000)))+(1764113 / 1000000000)*(94057489 / 100000000)+((40352153 / 10000000000)+(1764113 / 1000000000))*(5939131 / 100000000)+(47844391 / 1000000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
