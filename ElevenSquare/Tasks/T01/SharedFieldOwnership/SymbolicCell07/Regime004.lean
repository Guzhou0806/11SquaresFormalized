import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime004 : AnchoredWallDirectionCertificate := .ordinary facet010 facet014 [mirrorP08_010]

theorem regime004_guard : facet010.determinant facet014 ≠ 0 ∧
    (wallDualFirstPolynomial facet010 facet014 1).quartic.BernsteinNonnegCheck (0) (3/16) ∧
    (wallDualSecondPolynomial facet010 facet014 1).quartic.BernsteinNonnegCheck (0) (3/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet014]

theorem regime004_mirror08_010_margin0 : (wallDualMargin facet010 facet014 1 mirrorP08_010).BernsteinPosCheck (0) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet014, mirrorP08_010]

theorem regime004_mirror08_010 : WallDualCheck facet010 facet014 1 mirrorP08_010 (0) (3/16) := by
  rcases regime004_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime004_mirror08_010_margin0⟩

theorem regime004_point006_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP006 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP006]

theorem regime004_point007_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP007 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP007]

theorem regime004_point008_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP008 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP008]

theorem regime004_point009_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP009 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP009]

theorem regime004_point010_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP010 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP010]

theorem regime004_point011_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP011 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP011]

theorem regime004_point012_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP012 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP012]

theorem regime004_point013_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP013 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP013]

theorem regime004_point014_dominance : WallProjectionCheck 1 mirrorP08_010 ownedP014 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, ownedP014]

theorem regime004_mirror08_005_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_005 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_005]

theorem regime004_mirror08_006_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_006 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_006]

theorem regime004_mirror08_007_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_007 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_007]

theorem regime004_mirror08_008_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_008 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_008]

theorem regime004_mirror08_010_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_010 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_010]

theorem regime004_mirror08_011_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_011 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_011]

theorem regime004_mirror08_012_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_012 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_012]

theorem regime004_mirror08_013_dominance : WallProjectionCheck 1 mirrorP08_010 mirrorP08_013 (0) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_013]

theorem regime004_checked : regime004.Check 7 1 points (0) (3/16) := by
  unfold regime004 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet014_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime004_mirror08_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP08_010, by simp, regime004_point006_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point007_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point008_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point009_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point010_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point011_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point012_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point013_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_point014_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_005_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_006_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_007_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_008_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_010_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_011_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_012_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime004_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
