import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime007 : AnchoredWallDirectionCertificate := .ordinary facet010 facet011 [ownedP007, ownedP008]

theorem regime007_guard : facet010.determinant facet011 ≠ 0 ∧
    (wallDualFirstPolynomial facet010 facet011 1).quartic.BernsteinNonnegCheck (7/16) (1/2) ∧
    (wallDualSecondPolynomial facet010 facet011 1).quartic.BernsteinNonnegCheck (7/16) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet011]

theorem regime007_point007_margin0 : (wallDualMargin facet010 facet011 1 ownedP007).BernsteinPosCheck (7/16) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet011, ownedP007]

theorem regime007_point007 : WallDualCheck facet010 facet011 1 ownedP007 (7/16) (1/2) := by
  rcases regime007_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime007_point007_margin0⟩

theorem regime007_point008_margin0 : (wallDualMargin facet010 facet011 1 ownedP008).BernsteinPosCheck (7/16) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet011, ownedP008]

theorem regime007_point008 : WallDualCheck facet010 facet011 1 ownedP008 (7/16) (1/2) := by
  rcases regime007_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime007_point008_margin0⟩

theorem regime007_point006_dominance : WallProjectionCheck 1 ownedP007 ownedP006 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime007_point007_dominance : WallProjectionCheck 1 ownedP007 ownedP007 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime007_point008_dominance : WallProjectionCheck 1 ownedP008 ownedP008 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime007_point009_dominance : WallProjectionCheck 1 ownedP007 ownedP009 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime007_point010_dominance : WallProjectionCheck 1 ownedP007 ownedP010 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP010]

theorem regime007_point011_dominance : WallProjectionCheck 1 ownedP007 ownedP011 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP011]

theorem regime007_point012_dominance : WallProjectionCheck 1 ownedP007 ownedP012 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP012]

theorem regime007_point013_dominance : WallProjectionCheck 1 ownedP007 ownedP013 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP013]

theorem regime007_point014_dominance : WallProjectionCheck 1 ownedP007 ownedP014 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP014]

theorem regime007_mirror08_005_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_005 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_005]

theorem regime007_mirror08_006_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_006 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_006]

theorem regime007_mirror08_007_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_007 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_007]

theorem regime007_mirror08_008_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_008 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_008]

theorem regime007_mirror08_010_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_010 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_010]

theorem regime007_mirror08_011_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_011 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_011]

theorem regime007_mirror08_012_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_012 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_012]

theorem regime007_mirror08_013_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_013 (7/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_013]

theorem regime007_checked : regime007.Check 7 1 points (7/16) (1/2) := by
  unfold regime007 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime007_point007
    · exact regime007_point008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime007_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_point008_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_point010_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_point011_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_point012_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_point013_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_point014_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_mirror08_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_mirror08_006_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_mirror08_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_mirror08_008_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_mirror08_010_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_mirror08_011_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_mirror08_012_dominance⟩
    · exact ⟨ownedP007, by simp, regime007_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
