import ElevenSquare.Tasks.T06.ConcreteTaylorBase
import ElevenSquare.Tasks.T06.ConcreteTaylorIdentitiesRow55
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly02
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly09
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly17
import ElevenSquare.Tasks.T06.ConcreteTaylorPoly18
import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concreteRow55Alias0_curvature :
    gapRectangleCurvature constructionSquare focusedRadii (Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3) ≤ (rowCurvatures 55 : ℝ) := by
  have hA : |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (featureCenterDifference constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false })) (perp (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false })))| ≤ ((1118783 / 1000000) : ℝ) := by
    rw [concreteRow55Alias0_A0, concreteRow55Alias0_A1]
    exact (add_le_add concrete_abs_poly072 concrete_abs_poly071).trans (by norm_num)
  have hL : |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false })).1| + |(featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false })).2| ≤ ((1409217 / 1000000) : ℝ) := by
    rw [concreteRow55Alias0_L0, concreteRow55Alias0_L1]
    exact (add_le_add concrete_abs_poly074 concrete_abs_poly038).trans (by norm_num)
  have hC : |dot (cornerOffset constructionSquare 8 3) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| + |dot (perp (cornerOffset constructionSquare 8 3)) (featureNormal constructionSquare ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false }))| ≤ (1 : ℝ) := by
    rw [concreteRow55Alias0_C0, concreteRow55Alias0_C1]
    exact (add_le_add concrete_abs_poly009 concrete_abs_poly009).trans (by norm_num)
  have hK := concrete_feature_curvature_bound constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3
    ((1118783 / 1000000)) ((1409217 / 1000000)) (1)
    (fun j => (focusedRadii_bounds j).1.le) hA hL hC
  change featureRectangleCurvature constructionSquare focusedRadii ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3 ≤ ((1118783 / 1000000)+(1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)^2+2*((1409217 / 1000000)*((9356857 / 10000000000)+(678279 / 500000000)+((8671199 / 10000000000)+(4124329 / 5000000000))))*(35312013 / 10000000000)+1*((7549783 / 5000000000)+(35312013 / 10000000000))^2 at hK
  norm_num at hK
  exact hK.trans (by change _ ≤ (((79086693 / 1000000000000) : ℚ) : ℝ); norm_num)

theorem concreteRow55_curvature (g : Gap) (hg : g ∈ rowAliases 55) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures 55 : ℝ) := by
  change g ∈ [Gap.pair ({ owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false }) 3] at hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  · exact concreteRow55Alias0_curvature

end
end ElevenSquare.Tasks.T06
