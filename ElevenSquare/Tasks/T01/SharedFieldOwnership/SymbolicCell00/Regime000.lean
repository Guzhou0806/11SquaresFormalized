import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime000 : AnchoredWallDirectionCertificate := .ordinary facet009 facet013 [ownedP007]

theorem regime000_guard : facet009.determinant facet013 ≠ 0 ∧
    (wallDualFirstPolynomial facet009 facet013 0).quartic.BernsteinNonnegCheck (0) (1/16) ∧
    (wallDualSecondPolynomial facet009 facet013 0).quartic.BernsteinNonnegCheck (0) (1/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013]

theorem regime000_point007_margin0 : (wallDualMargin facet009 facet013 0 ownedP007).BernsteinPosCheck (0) (1/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013, ownedP007]

theorem regime000_point007 : WallDualCheck facet009 facet013 0 ownedP007 (0) (1/16) := by
  rcases regime000_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime000_point007_margin0⟩

theorem regime000_point005_dominance : WallProjectionCheck 0 ownedP007 ownedP005 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP005]

theorem regime000_point006_dominance : WallProjectionCheck 0 ownedP007 ownedP006 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime000_point007_dominance : WallProjectionCheck 0 ownedP007 ownedP007 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime000_point009_dominance : WallProjectionCheck 0 ownedP007 ownedP009 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime000_point010_dominance : WallProjectionCheck 0 ownedP007 ownedP010 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP010]

theorem regime000_mirror15_005_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_005 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_005]

theorem regime000_mirror15_007_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_007 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_007]

theorem regime000_mirror15_008_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_008 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_008]

theorem regime000_mirror15_009_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_009 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_009]

theorem regime000_mirror15_010_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_010 (0) (1/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_010]

theorem regime000_checked : regime000.Check 0 0 points (0) (1/16) := by
  unfold regime000 AnchoredWallDirectionCertificate.Check
  refine ⟨facet009_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime000_point007
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime000_point005_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_point007_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_point010_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror15_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror15_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror15_008_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror15_009_dominance⟩
    · exact ⟨ownedP007, by simp, regime000_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
