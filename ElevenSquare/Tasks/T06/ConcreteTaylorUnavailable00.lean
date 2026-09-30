import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesUnavailable00
import ElevenSquare.Tasks.T06.ConcreteTaylorNegative
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly04
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly12
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteUnavailable00_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 0) ≤ ((12613919 / 200000000000) : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((1724813 / 1000000) : ℝ) := by
    rw [concreteUnavailable00_A0, concreteUnavailable00_A1]
    exact (add_le_add concrete_abs_poly050 concrete_abs_poly016).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable00_L0, concreteUnavailable00_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 6 0) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 6 0)) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteUnavailable00_C0, concreteUnavailable00_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((1724813 / 1000000)) (1) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 0 ≤ ((1724813 / 1000000)+1*((678279 / 500000000)+(18767167 / 10000000000)+((4124329 / 5000000000)+(4435327 / 2000000000))))*(5670363 / 2500000000)^2+2*(1*((678279 / 500000000)+(18767167 / 10000000000)+((4124329 / 5000000000)+(4435327 / 2000000000))))*(5670363 / 2500000000)+(191 / 250)*((35312013 / 10000000000)+(5670363 / 2500000000))^2 at hK
  norm_num at hK
  exact hK.trans (by norm_num)

theorem concreteUnavailable00_negative (h : Displacement) (hh : InRectangle focusedRadii h) :
    gapValue T constructionSquare (Gap.pair ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 0) h < 0 := by
  have h0 : gapValue T constructionSquare (Gap.pair ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 0) 0 ≤ ((-25204999 / 100000000) : ℝ) := by
    rw [concreteUnavailable00_value]
    have hp := concrete_poly_upper_bound (![(-18 / 25), (291 / 200), (-51 / 50), (159 / 200), (8 / 5), (301 / 200), (-5 / 2), (37 / 40)]) ((-25204999 / 100000000))
      (by norm_num [polyUpper, Fin.sum_univ_succ])
    convert hp using 1 <;> norm_num
  have hL : |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteUnavailable00_L0, concreteUnavailable00_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hD : |dot (featureCenterDifference constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((7722539 / 10000000) : ℝ) := by
    rw [concreteUnavailable00_A1]
    exact concrete_abs_poly016
  have hC : |dot (perp (cornerOffset constructionSquare 6 0)) (featureNormal constructionSquare ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((5939131 / 100000000) : ℝ) := by
    rw [concreteUnavailable00_C1]
    exact concrete_abs_poly010
  apply concrete_feature_negative T constructionSquare focusedRadii ({ owner := 0, other := 6, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((-25204999 / 100000000)) (1) ((7722539 / 10000000)) ((5939131 / 100000000)) ((12613919 / 200000000000))
    (fun j => (focusedRadii_bounds j).1.le) h0 hL hD hC concreteUnavailable00_curvature ?_ h hh
  change (-25204999 / 100000000)+1*((678279 / 500000000)+(18767167 / 10000000000)+((4124329 / 5000000000)+(4435327 / 2000000000)))+(5670363 / 2500000000)*(7722539 / 10000000)+((35312013 / 10000000000)+(5670363 / 2500000000))*(5939131 / 100000000)+(12613919 / 200000000000)/2 < (0 : ℝ)
  norm_num

end
end ElevenSquare.Tasks.T06
