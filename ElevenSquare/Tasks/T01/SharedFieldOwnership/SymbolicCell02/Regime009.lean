import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime009 : AnchoredWallDirectionCertificate := .ordinary facet002 facet011 [ownedP006, mirrorP13_011]

theorem regime009_guard : facet002.determinant facet011 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet011 3).quartic.BernsteinNonnegCheck (0) (1/2) ∧
    (wallDualSecondPolynomial facet002 facet011 3).quartic.BernsteinNonnegCheck (0) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011]

theorem regime009_point006_margin0 : (wallDualMargin facet002 facet011 3 ownedP006).BernsteinPosCheck (0) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011, ownedP006]

theorem regime009_point006 : WallDualCheck facet002 facet011 3 ownedP006 (0) (1/2) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_point006_margin0⟩

theorem regime009_mirror13_011_margin0 : (wallDualMargin facet002 facet011 3 mirrorP13_011).BernsteinPosCheck (0) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011, mirrorP13_011]

theorem regime009_mirror13_011 : WallDualCheck facet002 facet011 3 mirrorP13_011 (0) (1/2) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_mirror13_011_margin0⟩

theorem regime009_point005_dominance : WallProjectionCheck 3 ownedP006 ownedP005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP005]

theorem regime009_point006_dominance : WallProjectionCheck 3 ownedP006 ownedP006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP006]

theorem regime009_point007_dominance : WallProjectionCheck 3 ownedP006 ownedP007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP007]

theorem regime009_point008_dominance : WallProjectionCheck 3 ownedP006 ownedP008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP008]

theorem regime009_point009_dominance : WallProjectionCheck 3 ownedP006 ownedP009 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP009]

theorem regime009_mirror13_005_dominance : WallProjectionCheck 3 ownedP006 mirrorP13_005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP13_005]

theorem regime009_mirror13_006_dominance : WallProjectionCheck 3 ownedP006 mirrorP13_006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP13_006]

theorem regime009_mirror13_007_dominance : WallProjectionCheck 3 ownedP006 mirrorP13_007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP13_007]

theorem regime009_mirror13_010_dominance : WallProjectionCheck 3 mirrorP13_011 mirrorP13_010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_011, mirrorP13_010]

theorem regime009_mirror13_011_dominance : WallProjectionCheck 3 mirrorP13_011 mirrorP13_011 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_011, mirrorP13_011]

theorem regime009_checked : regime009.Check 2 3 points (0) (1/2) := by
  unfold regime009 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime009_point006
    · exact regime009_mirror13_011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP006, by simp, regime009_point005_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_point006_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_point007_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_point008_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_point009_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_mirror13_005_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_mirror13_006_dominance⟩
    · exact ⟨ownedP006, by simp, regime009_mirror13_007_dominance⟩
    · exact ⟨mirrorP13_011, by simp, regime009_mirror13_010_dominance⟩
    · exact ⟨mirrorP13_011, by simp, regime009_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
