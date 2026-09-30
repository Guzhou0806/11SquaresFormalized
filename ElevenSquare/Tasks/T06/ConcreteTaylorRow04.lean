import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow04
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow04Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.wall 1 1 1) ≤ (rowCurvatures 4 : ℝ) := by
  have hC : |(cornerOffset constructionSquare 1 1).1| + |(cornerOffset constructionSquare 1 1).2| ≤ (1 : ℝ) := by
    rw [concreteRow04Alias0_C0, concreteRow04Alias0_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_wall_curvature_bound constructionSquare focusedRadii 1 1 (1) hC
  change wallRectangleCurvature constructionSquare focusedRadii 1 1 ≤ 1*((1764113 / 1000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((622419 / 200000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow04_curvature (g : Gap) (hg : g ∈ rowAliases 4) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 4 : ℝ) := by
  change g ∈ [Gap.wall 1 1 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow04Alias0_curvature

end
end ElevenSquare.Tasks.T06
