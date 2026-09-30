import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime010 : AnchoredWallDirectionCertificate := .ordinary facet002 facet011 [ownedP006, ownedP007]

theorem regime010_guard : facet002.determinant facet011 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet011 3).quartic.BernsteinNonnegCheck (1/2) (3/4) ∧
    (wallDualSecondPolynomial facet002 facet011 3).quartic.BernsteinNonnegCheck (1/2) (3/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011]

theorem regime010_point006_margin0 : (wallDualMargin facet002 facet011 3 ownedP006).BernsteinPosCheck (1/2) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011, ownedP006]

theorem regime010_point006 : WallDualCheck facet002 facet011 3 ownedP006 (1/2) (3/4) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point006_margin0⟩

theorem regime010_point007_margin0 : (wallDualMargin facet002 facet011 3 ownedP007).BernsteinPosCheck (1/2) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011, ownedP007]

theorem regime010_point007 : WallDualCheck facet002 facet011 3 ownedP007 (1/2) (3/4) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point007_margin0⟩

theorem regime010_point005_dominance : WallProjectionCheck 3 ownedP006 ownedP005 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP005]

theorem regime010_point006_dominance : WallProjectionCheck 3 ownedP006 ownedP006 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP006]

theorem regime010_point007_dominance : WallProjectionCheck 3 ownedP007 ownedP007 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime010_point008_dominance : WallProjectionCheck 3 ownedP006 ownedP008 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP008]

theorem regime010_point009_dominance : WallProjectionCheck 3 ownedP006 ownedP009 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP009]

theorem regime010_mirror13_005_dominance : WallProjectionCheck 3 ownedP007 mirrorP13_005 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_005]

theorem regime010_mirror13_006_dominance : WallProjectionCheck 3 ownedP006 mirrorP13_006 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP13_006]

theorem regime010_mirror13_007_dominance : WallProjectionCheck 3 ownedP006 mirrorP13_007 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP13_007]

theorem regime010_mirror13_010_dominance : WallProjectionCheck 3 ownedP006 mirrorP13_010 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP13_010]

theorem regime010_mirror13_011_dominance : WallProjectionCheck 3 ownedP006 mirrorP13_011 (1/2) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP13_011]

theorem regime010_checked : regime010.Check 2 3 points (1/2) (3/4) := by
  unfold regime010 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime010_point006
    · exact regime010_point007
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP006, by simp, regime010_point005_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_point007_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_point008_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror13_005_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_mirror13_006_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_mirror13_007_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_mirror13_010_dominance⟩
    · exact ⟨ownedP006, by simp, regime010_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
