import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime009 : AnchoredWallDirectionCertificate := .ordinary facet014 facet019 [ownedP013]

theorem regime009_guard : facet014.determinant facet019 ≠ 0 ∧
    (wallDualFirstPolynomial facet014 facet019 2).quartic.BernsteinNonnegCheck (0) (3/16) ∧
    (wallDualSecondPolynomial facet014 facet019 2).quartic.BernsteinNonnegCheck (0) (3/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet019]

theorem regime009_point013_margin0 : (wallDualMargin facet014 facet019 2 ownedP013).BernsteinPosCheck (0) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet019, ownedP013]

theorem regime009_point013 : WallDualCheck facet014 facet019 2 ownedP013 (0) (3/16) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_point013_margin0⟩

theorem regime009_point006_dominance : WallProjectionCheck 2 ownedP013 ownedP006 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP006]

theorem regime009_point007_dominance : WallProjectionCheck 2 ownedP013 ownedP007 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP007]

theorem regime009_point008_dominance : WallProjectionCheck 2 ownedP013 ownedP008 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP008]

theorem regime009_point009_dominance : WallProjectionCheck 2 ownedP013 ownedP009 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP009]

theorem regime009_point010_dominance : WallProjectionCheck 2 ownedP013 ownedP010 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP010]

theorem regime009_point011_dominance : WallProjectionCheck 2 ownedP013 ownedP011 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP011]

theorem regime009_point012_dominance : WallProjectionCheck 2 ownedP013 ownedP012 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP012]

theorem regime009_point013_dominance : WallProjectionCheck 2 ownedP013 ownedP013 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP013]

theorem regime009_point014_dominance : WallProjectionCheck 2 ownedP013 ownedP014 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP014]

theorem regime009_mirror08_005_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_005 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_005]

theorem regime009_mirror08_006_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_006 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_006]

theorem regime009_mirror08_007_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_007 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_007]

theorem regime009_mirror08_008_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_008 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_008]

theorem regime009_mirror08_010_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_010 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_010]

theorem regime009_mirror08_011_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_011 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_011]

theorem regime009_mirror08_012_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_012 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_012]

theorem regime009_mirror08_013_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_013 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_013]

theorem regime009_checked : regime009.Check 7 2 points (0) (3/16) := by
  unfold regime009 AnchoredWallDirectionCertificate.Check
  refine ⟨facet014_mem, facet019_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime009_point013
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP013, by simp, regime009_point006_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point007_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point008_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point009_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point010_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point011_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point012_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point013_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_point014_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_005_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_006_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_007_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_008_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_010_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_011_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_012_dominance⟩
    · exact ⟨ownedP013, by simp, regime009_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
