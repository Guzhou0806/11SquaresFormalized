import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow26
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

theorem concreteRow26Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 2) ≤ (rowCurvatures 26 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true })) (featureNormal constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (featureCenterDifference constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true })) (perp (featureNormal constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true })))| ≤ (1 : ℝ) := by
    rw [concreteRow26Alias0_A0, concreteRow26Alias0_A1]
    exact (add_le_add concrete_abs_poly003 concrete_abs_poly032).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true })).1| + |(featureNormal constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true })).2| ≤ (1 : ℝ) := by
    rw [concreteRow26Alias0_L0, concreteRow26Alias0_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 5 2) (featureNormal constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| + |dot (perp (cornerOffset constructionSquare 5 2)) (featureNormal constructionSquare ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }))| ≤ (1 : ℝ) := by
    rw [concreteRow26Alias0_C0, concreteRow26Alias0_C1]
    exact (add_le_add concrete_abs_poly058 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 2
    (1) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 2 ≤ (1+1*((12900283 / 10000000000)+(1635053 / 1000000000)+((534153 / 500000000)+(10683139 / 10000000000))))*(1890121 / 1250000000)^2+2*(1*((12900283 / 10000000000)+(1635053 / 1000000000)+((534153 / 500000000)+(10683139 / 10000000000))))*(1890121 / 1250000000)+1*((1890121 / 1250000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((13375661 / 500000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow26Alias1_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 1) ≤ (rowCurvatures 26 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false })) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false })))| ≤ (1 : ℝ) := by
    rw [concreteRow26Alias1_A0, concreteRow26Alias1_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly032).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false })).2| ≤ (1 : ℝ) := by
    rw [concreteRow26Alias1_L0, concreteRow26Alias1_L1]
    exact (add_le_add concrete_abs_poly032 concrete_abs_poly072).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 3 1) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 3 1)) (featureNormal constructionSquare ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteRow26Alias1_C0, concreteRow26Alias1_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly058).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 1
    (1) (1) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 1 ≤ (1+1*((1635053 / 1000000000)+(12900283 / 10000000000)+((10683139 / 10000000000)+(534153 / 500000000))))*(1890121 / 1250000000)^2+2*(1*((1635053 / 1000000000)+(12900283 / 10000000000)+((10683139 / 10000000000)+(534153 / 500000000))))*(1890121 / 1250000000)+1*((1890121 / 1250000000)+(1890121 / 1250000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((13375661 / 500000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow26_curvature (g : Gap) (hg : g ∈ rowAliases 26) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 26 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true }) 2, Gap.pair ({ owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false }) 1] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact concreteRow26Alias0_curvature
  · exact concreteRow26Alias1_curvature

end
end ElevenSquare.Tasks.T06
