import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable02
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly12
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly13
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable02_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ ((12613919 / 200000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((1724813 / 1000000) : ℝ) := by
    rw [concreteUnavailable02_A0, concreteUnavailable02_A1]
    exact (add_le_add concrete_abs_poly052 concrete_abs_poly050).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable02_L0, concreteUnavailable02_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 6 1) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 6 1)) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable02_C0, concreteUnavailable02_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((1724813 / 1000000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((1724813 / 1000000)+1*((678279 / 500000000)+(18767167 / 10000000000)+((4124329 / 5000000000)+(4435327 / 2000000000))))*(5670363 / 2500000000)^2+2*(1*((678279 / 500000000)+(18767167 / 10000000000)+((4124329 / 5000000000)+(4435327 / 2000000000))))*(5670363 / 2500000000)+(191 / 250)*((35312013 / 10000000000)+(5670363 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable02_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1) 0 ≤ ((-98843103 / 50000000) : ℝ) := by
    rw [concreteUnavailable02_value]
    have hp := concrete_poly_upper_bound (![(-36 / 25), (-71 / 25), (124 / 25), (-29 / 25), (-29 / 5), (-87 / 50), 5, (-19 / 10)]) ((-98843103 / 50000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable02_L0, concreteUnavailable02_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((47627909 / 50000000) : ℝ) := by
    rw [concreteUnavailable02_A1]
    exact concrete_abs_poly050
  have hC : |dot (perp (cornerOffset constructionSquare 6 1)) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable02_C1]
    exact concrete_abs_poly057
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 0, other := 6, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((-98843103 / 50000000)) (1) ((47627909 / 50000000)) ((5939131 / 100000000)) ((12613919 / 200000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable02_curvature ?_ h hh
  change (-98843103 / 50000000)+1*((678279 / 500000000)+(18767167 / 10000000000)+((4124329 / 5000000000)+(4435327 / 2000000000)))+(5670363 / 2500000000)*(47627909 / 50000000)+((35312013 / 10000000000)+(5670363 / 2500000000))*(5939131 / 100000000)+(12613919 / 200000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
