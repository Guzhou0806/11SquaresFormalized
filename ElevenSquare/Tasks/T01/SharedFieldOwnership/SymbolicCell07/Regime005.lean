import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime005 : AnchoredWallDirectionCertificate := .ordinary facet010 facet014 [ownedP007, mirrorP08_010]

theorem regime005_guard : facet010.determinant facet014 ≠ 0 ∧
    (wallDualFirstPolynomial facet010 facet014 1).quartic.BernsteinNonnegCheck (3/16) (1/4) ∧
    (wallDualSecondPolynomial facet010 facet014 1).quartic.BernsteinNonnegCheck (3/16) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet014]

theorem regime005_point007_margin0 : (wallDualMargin facet010 facet014 1 ownedP007).BernsteinPosCheck (3/16) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet014, ownedP007]

theorem regime005_point007 : WallDualCheck facet010 facet014 1 ownedP007 (3/16) (1/4) := by
  rcases regime005_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime005_point007_margin0⟩

theorem regime005_mirror08_010_margin0 : (wallDualMargin facet010 facet014 1 mirrorP08_010).BernsteinPosCheck (3/16) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet014, mirrorP08_010]

theorem regime005_mirror08_010 : WallDualCheck facet010 facet014 1 mirrorP08_010 (3/16) (1/4) := by
  rcases regime005_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime005_mirror08_010_margin0⟩

theorem regime005_point006_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP006]

theorem regime005_point007_dominance : WallProjectionCheck 1 ownedP007 ownedP007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime005_point008_dominance : WallProjectionCheck 1 ownedP007 ownedP008 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP008]

theorem regime005_point009_dominance : WallProjectionCheck 1 ownedP007 ownedP009 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime005_point010_dominance : WallProjectionCheck 1 ownedP007 ownedP010 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP010]

theorem regime005_point011_dominance : WallProjectionCheck 1 ownedP007 ownedP011 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP011]

theorem regime005_point012_dominance : WallProjectionCheck 1 ownedP007 ownedP012 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP012]

theorem regime005_point013_dominance : WallProjectionCheck 1 ownedP007 ownedP013 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP013]

theorem regime005_point014_dominance : WallProjectionCheck 1 ownedP007 ownedP014 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP014]

theorem regime005_mirror08_005_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_005 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_005]

theorem regime005_mirror08_006_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_006]

theorem regime005_mirror08_007_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_007]

theorem regime005_mirror08_008_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_008 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_008]

theorem regime005_mirror08_010_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_010 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_010]

theorem regime005_mirror08_011_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_011 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_011]

theorem regime005_mirror08_012_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_012 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_012]

theorem regime005_mirror08_013_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_013 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_013]

theorem regime005_checked : regime005.Check 7 1 points (3/16) (1/4) := by
  unfold regime005 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet014_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime005_point007
    · exact regime005_mirror08_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP08_010, by simp, regime005_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point007_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point008_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point010_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point011_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point012_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point013_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_point014_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_mirror08_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_mirror08_006_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_mirror08_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_mirror08_008_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime005_mirror08_010_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_mirror08_011_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_mirror08_012_dominance⟩
    · exact ⟨ownedP007, by simp, regime005_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
