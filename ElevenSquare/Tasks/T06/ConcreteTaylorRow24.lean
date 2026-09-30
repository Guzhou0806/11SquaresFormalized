import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow24
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly00
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly08
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly14
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow24Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0) ≤ (rowCurvatures 24 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })))| ≤ (1 : ℝ) := by
    rw [concreteRow24Alias0_A0, concreteRow24Alias0_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteRow24Alias0_L0, concreteRow24Alias0_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 4 0) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 4 0)) (featureNormal constructionSquare ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteRow24Alias0_C0, concreteRow24Alias0_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0
    (1) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0 ≤ (1+1*((4087019 / 2500000000)+(1635053 / 1000000000)+((13962901 / 10000000000)+(10683139 / 10000000000))))*(1890121 / 1250000000)^2+2*(1*((4087019 / 2500000000)+(1635053 / 1000000000)+((13962901 / 10000000000)+(10683139 / 10000000000))))*(1890121 / 1250000000)+1*((20161291 / 10000000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((19829653 / 500000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow24Alias1_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1) ≤ (rowCurvatures 24 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteRow24Alias1_A0, concreteRow24Alias1_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly032).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteRow24Alias1_L0, concreteRow24Alias1_L1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 3 1) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 3 1)) (featureNormal constructionSquare ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteRow24Alias1_C0, concreteRow24Alias1_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1
    (1) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1 ≤ (1+1*((1635053 / 1000000000)+(4087019 / 2500000000)+((10683139 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)^2+2*(1*((1635053 / 1000000000)+(4087019 / 2500000000)+((10683139 / 10000000000)+(13962901 / 10000000000))))*(20161291 / 10000000000)+1*((1890121 / 1250000000)+(20161291 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((19829653 / 500000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow24_curvature (g : Gap) (hg : g ∈ rowAliases 24) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 24 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false }) 0, Gap.pair ({ owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact concreteRow24Alias0_curvature
  · exact concreteRow24Alias1_curvature

end
end ElevenSquare.Tasks.T06
