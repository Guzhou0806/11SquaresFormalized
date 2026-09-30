import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow13
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow13Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.wall 3 3 3) ≤ (rowCurvatures 13 : ℝ) := by
  have hC : |(cornerOffset constructionSquare 3 3).1| + |(cornerOffset constructionSquare 3 3).2| ≤ (1 : ℝ) := by
    rw [concreteRow13Alias0_C0, concreteRow13Alias0_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_wall_curvature_bound constructionSquare focusedRadii 3 3 (1) hC
  change wallRectangleCurvature constructionSquare focusedRadii 3 3 ≤ 1*((1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((2286437 / 1000000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow13_curvature (g : Gap) (hg : g ∈ rowAliases 13) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 13 : ℝ) := by
  change g ∈ [Gap.wall 3 3 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow13Alias0_curvature

end
end ElevenSquare.Tasks.T06
