import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow19
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow19Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.wall 10 1 1) ≤ (rowCurvatures 19 : ℝ) := by
  have hC : |(cornerOffset constructionSquare 10 1).1| + |(cornerOffset constructionSquare 10 1).2| ≤ ((191 / 250) : ℝ) := by
    rw [concreteRow19Alias0_C0, concreteRow19Alias0_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_wall_curvature_bound constructionSquare focusedRadii 10 1 ((191 / 250)) hC
  change wallRectangleCurvature constructionSquare focusedRadii 10 1 ≤ (191 / 250)*((67647473 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((1748101 / 50000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow19_curvature (g : Gap) (hg : g ∈ rowAliases 19) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 19 : ℝ) := by
  change g ∈ [Gap.wall 10 1 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow19Alias0_curvature

end
end ElevenSquare.Tasks.T06
