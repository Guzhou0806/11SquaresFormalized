import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow46
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly07
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow46Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ (rowCurvatures 46 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((83361 / 62500) : ℝ) := by
    rw [concreteRow46Alias0_A0, concreteRow46Alias0_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly031).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow46Alias0_L0, concreteRow46Alias0_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 1) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 9 1)) (featureNormal constructionSquare ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteRow46Alias0_C0, concreteRow46Alias0_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((83361 / 62500)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((83361 / 62500)+(1409217 / 1000000)*((293551 / 400000000)+(1920157 / 2500000000)+((10335557 / 10000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)^2+2*((1409217 / 1000000)*((293551 / 400000000)+(1920157 / 2500000000)+((10335557 / 10000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)+1*((40352153 / 10000000000)+(67647473 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((72275923 / 250000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow46_curvature (g : Gap) (hg : g ∈ rowAliases 46) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 46 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow46Alias0_curvature

end
end ElevenSquare.Tasks.T06
