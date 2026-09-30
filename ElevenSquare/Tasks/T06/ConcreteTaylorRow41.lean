import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow41
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow41Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ (rowCurvatures 41 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((83361 / 62500) : ℝ) := by
    rw [concreteRow41Alias0_A0, concreteRow41Alias0_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly033).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow41Alias0_L0, concreteRow41Alias0_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 10 3) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 10 3)) (featureNormal constructionSquare ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteRow41Alias0_C0, concreteRow41Alias0_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((83361 / 62500)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ ((83361 / 62500)+(1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((1920157 / 2500000000)+(293551 / 400000000)+((8222903 / 2500000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+1*((67647473 / 10000000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((51183607 / 250000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow41_curvature (g : Gap) (hg : g ∈ rowAliases 41) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 41 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false }) 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow41Alias0_curvature

end
end ElevenSquare.Tasks.T06
