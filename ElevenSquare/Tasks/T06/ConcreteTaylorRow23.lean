import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow23
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

theorem concreteRow23Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1) ≤ (rowCurvatures 23 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false })))| ≤ ((692171 / 500000) : ℝ) := by
    rw [concreteRow23Alias0_A0, concreteRow23Alias0_A1]
    exact (add_le_add concrete_abs_poly075 concrete_abs_poly022).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow23Alias0_L0, concreteRow23Alias0_L1]
    exact (add_le_add concrete_abs_poly026 concrete_abs_poly074).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 2 1) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 2 1)) (featureNormal constructionSquare ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }))| ≤ ((191 / 250) : ℝ) := by
    rw [concreteRow23Alias0_C0, concreteRow23Alias0_C1]
    exact (add_le_add concrete_abs_poly007 concrete_abs_poly057).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1
    ((692171 / 500000)) ((1409217 / 1000000)) ((191 / 250))
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1 ≤ ((692171 / 500000)+(1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)^2+2*((1409217 / 1000000)*((8962451 / 10000000000)+(1920157 / 2500000000)+((5212397 / 5000000000)+(8222903 / 2500000000))))*(67647473 / 10000000000)+(191 / 250)*((5670363 / 2500000000)+(67647473 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((12019627 / 50000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow23_curvature (g : Gap) (hg : g ∈ rowAliases 23) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 23 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow23Alias0_curvature

end
end ElevenSquare.Tasks.T06
