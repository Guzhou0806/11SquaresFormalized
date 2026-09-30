import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime007 : AnchoredWallDirectionCertificate := .crossing facet013 facet008 facet002 (286195087637/536422000000) [mirrorP14_008]

theorem regime007_guard : facet013.determinant facet008 ≠ 0 ∧
    facet008.determinant facet002 ≠ 0 ∧
    0 < (286195087637/536422000000:ℚ) ∧
    wallDualSecondPolynomial facet008 facet002 2 = (wallDualFirstPolynomial facet013 facet008 2).negScale (286195087637/536422000000) ∧
    (wallDualSecondPolynomial facet013 facet008 2).quartic.BernsteinNonnegCheck (1/2) (1) ∧
    (wallDualFirstPolynomial facet008 facet002 2).quartic.BernsteinNonnegCheck (1/2) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet008, facet002]

theorem regime007_mirror14_008_margin0 : (wallDualMargin facet013 facet008 2 mirrorP14_008).BernsteinPosCheck (1/2) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet008, facet002, mirrorP14_008]

theorem regime007_mirror14_008_margin1 : (wallDualMargin facet008 facet002 2 mirrorP14_008).BernsteinPosCheck (1/2) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet008, facet002, mirrorP14_008]

theorem regime007_mirror14_008 : WallDualCrossingCheck facet013 facet008 facet002 2 mirrorP14_008 (1/2) (1) (286195087637/536422000000) := by
  rcases regime007_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime007_mirror14_008_margin0, regime007_mirror14_008_margin1⟩

theorem regime007_point005_dominance : WallProjectionCheck 2 mirrorP14_008 ownedP005 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, ownedP005]

theorem regime007_point006_dominance : WallProjectionCheck 2 mirrorP14_008 ownedP006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, ownedP006]

theorem regime007_point007_dominance : WallProjectionCheck 2 mirrorP14_008 ownedP007 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, ownedP007]

theorem regime007_point008_dominance : WallProjectionCheck 2 mirrorP14_008 ownedP008 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, ownedP008]

theorem regime007_mirror14_005_dominance : WallProjectionCheck 2 mirrorP14_008 mirrorP14_005 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_005]

theorem regime007_mirror14_006_dominance : WallProjectionCheck 2 mirrorP14_008 mirrorP14_006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_006]

theorem regime007_mirror14_008_dominance : WallProjectionCheck 2 mirrorP14_008 mirrorP14_008 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_008]

theorem regime007_mirror14_009_dominance : WallProjectionCheck 2 mirrorP14_008 mirrorP14_009 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_009]

theorem regime007_checked : regime007.Check 1 2 points (1/2) (1) := by
  unfold regime007 AnchoredWallDirectionCertificate.Check
  refine ⟨facet013_mem, facet008_mem, facet002_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime007_mirror14_008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP14_008, by simp, regime007_point005_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime007_point006_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime007_point007_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime007_point008_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime007_mirror14_005_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime007_mirror14_006_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime007_mirror14_008_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime007_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
