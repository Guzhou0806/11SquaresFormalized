import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime000 : AnchoredWallDirectionCertificate := .ordinary facet011 facet015 [ownedP007, ownedP008]

theorem regime000_guard : facet011.determinant facet015 ≠ 0 ∧
    (wallDualFirstPolynomial facet011 facet015 0).quartic.BernsteinNonnegCheck (0) (3/16) ∧
    (wallDualSecondPolynomial facet011 facet015 0).quartic.BernsteinNonnegCheck (0) (3/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015]

theorem regime000_point007_margin0 : (wallDualMargin facet011 facet015 0 ownedP007).BernsteinPosCheck (0) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015, ownedP007]

theorem regime000_point007 : WallDualCheck facet011 facet015 0 ownedP007 (0) (3/16) := by
  rcases regime000_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime000_point007_margin0⟩

theorem regime000_point008_margin0 : (wallDualMargin facet011 facet015 0 ownedP008).BernsteinPosCheck (0) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015, ownedP008]

theorem regime000_point008 : WallDualCheck facet011 facet015 0 ownedP008 (0) (3/16) := by
  rcases regime000_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime000_point008_margin0⟩

theorem regime000_point005_dominance : WallProjectionCheck 0 ownedP007 ownedP005 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP005]

theorem regime000_point006_dominance : WallProjectionCheck 0 ownedP007 ownedP006 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime000_point007_dominance : WallProjectionCheck 0 ownedP007 ownedP007 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime000_point008_dominance : WallProjectionCheck 0 ownedP008 ownedP008 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime000_point009_dominance : WallProjectionCheck 0 ownedP007 ownedP009 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime000_mirror13_005_dominance : WallProjectionCheck 0 ownedP007 mirrorP13_005 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_005]

theorem regime000_mirror13_006_dominance : WallProjectionCheck 0 ownedP008 mirrorP13_006 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP13_006]

theorem regime000_mirror13_007_dominance : WallProjectionCheck 0 ownedP007 mirrorP13_007 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_007]

theorem regime000_mirror13_010_dominance : WallProjectionCheck 0 ownedP007 mirrorP13_010 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_010]

theorem regime000_mirror13_011_dominance : WallProjectionCheck 0 ownedP007 mirrorP13_011 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_011]

theorem regime000_checked : regime000.Check 2 0 points (0) (3/16) := by
  unfold regime000 AnchoredWallDirectionCertificate.Check
  refine ⟨facet011_mem, facet015_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime000_point007
    · exact regime000_point008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime000_point005_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_point008_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror13_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime000_mirror13_006_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror13_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror13_010_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
