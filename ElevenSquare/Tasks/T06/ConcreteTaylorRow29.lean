import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow29
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow29Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3) ≤ (rowCurvatures 29 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true })))| ≤ (2 : ℝ) := by
    rw [concreteRow29Alias0_A0, concreteRow29Alias0_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly072).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteRow29Alias0_L0, concreteRow29Alias0_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 5 3) (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 5 3)) (featureNormal constructionSquare ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteRow29Alias0_C0, concreteRow29Alias0_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3
    (2) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3 ≤ (2+1*((12900283 / 10000000000)+(4087019 / 2500000000)+((534153 / 500000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)^2+2*(1*((12900283 / 10000000000)+(4087019 / 2500000000)+((534153 / 500000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)+1*((1890121 / 1250000000)+(20161291 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((2116571 / 50000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow29_curvature (g : Gap) (hg : g ∈ rowAliases 29) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 29 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow29Alias0_curvature

end
end ElevenSquare.Tasks.T06
