import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime009 : AnchoredWallDirectionCertificate := .ordinary facet002 facet009 [ownedP007, mirrorP15_005]

theorem regime009_guard : facet002.determinant facet009 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet009 3).quartic.BernsteinNonnegCheck (0) (1/2) ∧
    (wallDualSecondPolynomial facet002 facet009 3).quartic.BernsteinNonnegCheck (0) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009]

theorem regime009_point007_margin0 : (wallDualMargin facet002 facet009 3 ownedP007).BernsteinPosCheck (0) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009, ownedP007]

theorem regime009_point007 : WallDualCheck facet002 facet009 3 ownedP007 (0) (1/2) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_point007_margin0⟩

theorem regime009_mirror15_005_margin0 : (wallDualMargin facet002 facet009 3 mirrorP15_005).BernsteinPosCheck (0) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009, mirrorP15_005]

theorem regime009_mirror15_005 : WallDualCheck facet002 facet009 3 mirrorP15_005 (0) (1/2) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_mirror15_005_margin0⟩

theorem regime009_point005_dominance : WallProjectionCheck 3 ownedP007 ownedP005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP005]

theorem regime009_point006_dominance : WallProjectionCheck 3 ownedP007 ownedP006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime009_point007_dominance : WallProjectionCheck 3 ownedP007 ownedP007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime009_point009_dominance : WallProjectionCheck 3 ownedP007 ownedP009 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime009_point010_dominance : WallProjectionCheck 3 ownedP007 ownedP010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP010]

theorem regime009_mirror15_005_dominance : WallProjectionCheck 3 mirrorP15_005 mirrorP15_005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_005, mirrorP15_005]

theorem regime009_mirror15_007_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_007]

theorem regime009_mirror15_008_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_008]

theorem regime009_mirror15_009_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_009 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_009]

theorem regime009_mirror15_010_dominance : WallProjectionCheck 3 mirrorP15_005 mirrorP15_010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_005, mirrorP15_010]

theorem regime009_checked : regime009.Check 0 3 points (0) (1/2) := by
  unfold regime009 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet009_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime009_point007
    · exact regime009_mirror15_005
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime009_point005_dominance⟩
    · exact ⟨ownedP007, by simp, regime009_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime009_point007_dominance⟩
    · exact ⟨ownedP007, by simp, regime009_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime009_point010_dominance⟩
    · exact ⟨mirrorP15_005, by simp, regime009_mirror15_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime009_mirror15_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime009_mirror15_008_dominance⟩
    · exact ⟨ownedP007, by simp, regime009_mirror15_009_dominance⟩
    · exact ⟨mirrorP15_005, by simp, regime009_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
