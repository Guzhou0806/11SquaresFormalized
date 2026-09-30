import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow06Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.wall 1 0 2) ≤ (rowCurvatures 6 : ℝ) := by
  have hC : |(cornerOffset constructionSquare 1 0).1| + |(cornerOffset constructionSquare 1 0).2| ≤ (1 : ℝ) := by
    rw [concreteRow06Alias0_C0, concreteRow06Alias0_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_wall_curvature_bound constructionSquare focusedRadii 1 0 (1) hC
  change wallRectangleCurvature constructionSquare focusedRadii 1 0 ≤ 1*((1764113 / 1000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((622419 / 200000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow06_curvature (g : Gap) (hg : g ∈ rowAliases 6) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 6 : ℝ) := by
  change g ∈ [Gap.wall 1 0 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow06Alias0_curvature

end
end ElevenSquare.Tasks.T06
