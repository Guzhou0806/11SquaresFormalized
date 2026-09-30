import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow30
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly05
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly06
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow30Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1) ≤ (rowCurvatures 30 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((1620343 / 1000000) : ℝ) := by
    rw [concreteRow30Alias0_A0, concreteRow30Alias0_A1]
    exact (add_le_add concrete_abs_poly075 concrete_abs_poly023).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow30Alias0_L0, concreteRow30Alias0_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 4 1) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 4 1)) (featureNormal constructionSquare ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteRow30Alias0_C0, concreteRow30Alias0_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((1620343 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1 ≤ ((1620343 / 1000000)+(1409217 / 1000000)*((4087019 / 2500000000)+(9356857 / 10000000000)+((13962901 / 10000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)^2+2*((1409217 / 1000000)*((4087019 / 2500000000)+(9356857 / 10000000000)+((13962901 / 10000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)+(191 / 250)*((20161291 / 10000000000)+(7549783 / 5000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((6756119 / 200000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow30_curvature (g : Gap) (hg : g ∈ rowAliases 30) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 30 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow30Alias0_curvature

end
end ElevenSquare.Tasks.T06
