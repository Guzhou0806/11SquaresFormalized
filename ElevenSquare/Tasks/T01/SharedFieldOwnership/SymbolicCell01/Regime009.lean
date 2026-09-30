import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime009 : AnchoredWallDirectionCertificate := .ordinary facet002 facet010 [ownedP006]

theorem regime009_guard : facet002.determinant facet010 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet010 3).quartic.BernsteinNonnegCheck (3/4) (7/8) ∧
    (wallDualSecondPolynomial facet002 facet010 3).quartic.BernsteinNonnegCheck (3/4) (7/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010]

theorem regime009_point006_margin0 : (wallDualMargin facet002 facet010 3 ownedP006).BernsteinPosCheck (3/4) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, ownedP006]

theorem regime009_point006 : WallDualCheck facet002 facet010 3 ownedP006 (3/4) (7/8) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_point006_margin0⟩

theorem regime009_point005_dominance : WallProjectionCheck 3 ownedP006 ownedP005 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP005]

theorem regime009_point006_dominance : WallProjectionCheck 3 ownedP006 ownedP006 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP006]

theorem regime009_point007_dominance : WallProjectionCheck 3 ownedP006 ownedP007 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP007]

theorem regime009_point008_dominance : WallProjectionCheck 3 ownedP006 ownedP008 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP008]

theorem regime009_mirror14_005_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_005 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_005]

theorem regime009_mirror14_006_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_006 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_006]

theorem regime009_mirror14_008_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_008 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_008]

theorem regime009_mirror14_009_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_009 (3/4) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_009]

theorem regime009_checked : regime009.Check 1 3 points (3/4) (7/8) := by
  unfold regime009 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime009_point006
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP006, by simp, regime009_point005_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_point006_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_point007_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_point008_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_mirror14_005_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_mirror14_006_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_mirror14_008_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
