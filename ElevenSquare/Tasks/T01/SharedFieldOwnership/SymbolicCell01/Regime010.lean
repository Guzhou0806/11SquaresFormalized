import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime010 : AnchoredWallDirectionCertificate := .ordinary facet002 facet010 [ownedP006, ownedP007]

theorem regime010_guard : facet002.determinant facet010 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet010 3).quartic.BernsteinNonnegCheck (7/8) (1) ∧
    (wallDualSecondPolynomial facet002 facet010 3).quartic.BernsteinNonnegCheck (7/8) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010]

theorem regime010_point006_margin0 : (wallDualMargin facet002 facet010 3 ownedP006).BernsteinPosCheck (7/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, ownedP006]

theorem regime010_point006 : WallDualCheck facet002 facet010 3 ownedP006 (7/8) (1) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point006_margin0⟩

theorem regime010_point007_margin0 : (wallDualMargin facet002 facet010 3 ownedP007).BernsteinPosCheck (7/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, ownedP007]

theorem regime010_point007 : WallDualCheck facet002 facet010 3 ownedP007 (7/8) (1) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point007_margin0⟩

theorem regime010_point005_dominance : WallProjectionCheck 3 ownedP006 ownedP005 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP005]

theorem regime010_point006_dominance : WallProjectionCheck 3 ownedP006 ownedP006 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP006]

theorem regime010_point007_dominance : WallProjectionCheck 3 ownedP007 ownedP007 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime010_point008_dominance : WallProjectionCheck 3 ownedP007 ownedP008 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP008]

theorem regime010_mirror14_005_dominance : WallProjectionCheck 3 ownedP007 mirrorP14_005 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP14_005]

theorem regime010_mirror14_006_dominance : WallProjectionCheck 3 ownedP007 mirrorP14_006 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP14_006]

theorem regime010_mirror14_008_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_008 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_008]

theorem regime010_mirror14_009_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_009 (7/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_009]

theorem regime010_checked : regime010.Check 1 3 points (7/8) (1) := by
  unfold regime010 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime010_point006
    · exact regime010_point007
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP006, by simp, regime010_point005_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_point007_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_point008_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror14_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror14_006_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_mirror14_008_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
