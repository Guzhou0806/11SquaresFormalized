import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow48
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow48Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0) ≤ (rowCurvatures 48 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((8199 / 8000) : ℝ) := by
    rw [concreteRow48Alias0_A0, concreteRow48Alias0_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly024).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow48Alias0_L0, concreteRow48Alias0_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 0) (featureNormal constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 8 0)) (featureNormal constructionSquare ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteRow48Alias0_C0, concreteRow48Alias0_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0
    ((8199 / 8000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0 ≤ ((8199 / 8000)+(1409217 / 1000000)*((9356857 / 10000000000)+(293551 / 400000000)+((8671199 / 10000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((9356857 / 10000000000)+(293551 / 400000000)+((8671199 / 10000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+1*((7549783 / 5000000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((4406157 / 50000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow48_curvature (g : Gap) (hg : g ∈ rowAliases 48) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 48 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false }) 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow48Alias0_curvature

end
end ElevenSquare.Tasks.T06
