import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow22
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly01
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly10
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow22Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0) ≤ (rowCurvatures 22 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((1742993 / 1000000) : ℝ) := by
    rw [concreteRow22Alias0_A0, concreteRow22Alias0_A1]
    exact (add_le_add concrete_abs_poly075 concrete_abs_poly041).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow22Alias0_L0, concreteRow22Alias0_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 2 0) (featureNormal constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 2 0)) (featureNormal constructionSquare ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteRow22Alias0_C0, concreteRow22Alias0_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0
    ((1742993 / 1000000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0 ≤ ((1742993 / 1000000)+(1409217 / 1000000)*((8962451 / 10000000000)+(9356857 / 10000000000)+((5212397 / 5000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)^2+2*((1409217 / 1000000)*((8962451 / 10000000000)+(9356857 / 10000000000)+((5212397 / 5000000000)+(8671199 / 10000000000))))*(7549783 / 5000000000)+(191 / 250)*((5670363 / 2500000000)+(7549783 / 5000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((30814247 / 1000000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow22_curvature (g : Gap) (hg : g ∈ rowAliases 22) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 22 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false }) 0] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow22Alias0_curvature

end
end ElevenSquare.Tasks.T06
