import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow38
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly10
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow38Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2) ≤ (rowCurvatures 38 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((8199 / 8000) : ℝ) := by
    rw [concreteRow38Alias0_A0, concreteRow38Alias0_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly043).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow38Alias0_L0, concreteRow38Alias0_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 9 2) (featureNormal constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 9 2)) (featureNormal constructionSquare ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteRow38Alias0_C0, concreteRow38Alias0_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2
    ((8199 / 8000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2 ≤ ((8199 / 8000)+(1409217 / 1000000)*((293551 / 400000000)+(9356857 / 10000000000)+((10335557 / 10000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)^2+2*((1409217 / 1000000)*((293551 / 400000000)+(9356857 / 10000000000)+((10335557 / 10000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)+1*((40352153 / 10000000000)+(7549783 / 5000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((24145499 / 500000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow38_curvature (g : Gap) (hg : g ∈ rowAliases 38) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 38 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true }) 2] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow38Alias0_curvature

end
end ElevenSquare.Tasks.T06
