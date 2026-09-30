import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime000 : AnchoredWallDirectionCertificate := .crossing facet002 facet010 facet013 (260419500000/139669658299) [ownedP008]

theorem regime000_guard : facet002.determinant facet010 ≠ 0 ∧
    facet010.determinant facet013 ≠ 0 ∧
    0 < (260419500000/139669658299:ℚ) ∧
    wallDualSecondPolynomial facet010 facet013 0 = (wallDualFirstPolynomial facet002 facet010 0).negScale (260419500000/139669658299) ∧
    (wallDualSecondPolynomial facet002 facet010 0).quartic.BernsteinNonnegCheck (0) (7/16) ∧
    (wallDualFirstPolynomial facet010 facet013 0).quartic.BernsteinNonnegCheck (0) (7/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, facet013]

theorem regime000_point008_margin0 : (wallDualMargin facet002 facet010 0 ownedP008).BernsteinPosCheck (0) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, facet013, ownedP008]

theorem regime000_point008_margin1 : (wallDualMargin facet010 facet013 0 ownedP008).BernsteinPosCheck (0) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, facet013, ownedP008]

theorem regime000_point008 : WallDualCrossingCheck facet002 facet010 facet013 0 ownedP008 (0) (7/16) (260419500000/139669658299) := by
  rcases regime000_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime000_point008_margin0, regime000_point008_margin1⟩

theorem regime000_point005_dominance : WallProjectionCheck 0 ownedP008 ownedP005 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP005]

theorem regime000_point006_dominance : WallProjectionCheck 0 ownedP008 ownedP006 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime000_point007_dominance : WallProjectionCheck 0 ownedP008 ownedP007 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime000_point008_dominance : WallProjectionCheck 0 ownedP008 ownedP008 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime000_mirror14_005_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_005 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_005]

theorem regime000_mirror14_006_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_006 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_006]

theorem regime000_mirror14_008_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_008 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_008]

theorem regime000_mirror14_009_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_009 (0) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_009]

theorem regime000_checked : regime000.Check 1 0 points (0) (7/16) := by
  unfold regime000 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet010_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime000_point008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime000_point005_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_point008_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_mirror14_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_mirror14_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_mirror14_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
