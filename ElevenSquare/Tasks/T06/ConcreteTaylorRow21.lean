import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow21
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly15
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow21Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3) ≤ (rowCurvatures 21 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true })))| ≤ ((1236001 / 1000000) : ℝ) := by
    rw [concreteRow21Alias0_A0, concreteRow21Alias0_A1]
    exact (add_le_add concrete_abs_poly001 concrete_abs_poly025).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow21Alias0_L0, concreteRow21Alias0_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 1 3) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 1 3)) (featureNormal constructionSquare ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteRow21Alias0_C0, concreteRow21Alias0_C1]
    exact (add_le_add concrete_abs_poly061 concrete_abs_poly010).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3
    ((1236001 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3 ≤ ((1236001 / 1000000)+(1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)^2+2*((1409217 / 1000000)*((1636033 / 1000000000)+(293551 / 400000000)+((6880181 / 5000000000)+(10335557 / 10000000000))))*(40352153 / 10000000000)+(191 / 250)*((1764113 / 1000000000)+(40352153 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((100287661 / 1000000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow21_curvature (g : Gap) (hg : g ∈ rowAliases 21) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 21 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true }) 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow21Alias0_curvature

end
end ElevenSquare.Tasks.T06
