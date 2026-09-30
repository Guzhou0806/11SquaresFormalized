import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow36
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow36Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ (rowCurvatures 36 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteRow36Alias0_A0, concreteRow36Alias0_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly004).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow36Alias0_L0, concreteRow36Alias0_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 7 1) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 7 1)) (featureNormal constructionSquare ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteRow36Alias0_C0, concreteRow36Alias0_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((11182451 / 10000000000)+(293551 / 400000000)+((3232837 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((11182451 / 10000000000)+(293551 / 400000000)+((3232837 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+1*((8824483 / 2500000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((23139939 / 200000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow36_curvature (g : Gap) (hg : g ∈ rowAliases 36) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 36 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow36Alias0_curvature

end
end ElevenSquare.Tasks.T06
