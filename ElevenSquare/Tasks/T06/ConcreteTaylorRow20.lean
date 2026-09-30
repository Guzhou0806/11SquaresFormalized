import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow20
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow20Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2) ≤ (rowCurvatures 20 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((1434091 / 1000000) : ℝ) := by
    rw [concreteRow20Alias0_A0, concreteRow20Alias0_A1]
    exact (add_le_add concrete_abs_poly001 concrete_abs_poly039).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow20Alias0_L0, concreteRow20Alias0_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 0 2) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 0 2)) (featureNormal constructionSquare ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteRow20Alias0_C0, concreteRow20Alias0_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2
    ((1434091 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2 ≤ ((1434091 / 1000000)+(1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((18767167 / 10000000000)+(678279 / 500000000)+((4435327 / 2000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+(191 / 250)*((5670363 / 2500000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((13268419 / 125000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow20_curvature (g : Gap) (hg : g ∈ rowAliases 20) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 20 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true }) 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow20Alias0_curvature

end
end ElevenSquare.Tasks.T06
