import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime010 : AnchoredWallDirectionCertificate := .ordinary facet002 facet009 [ownedP007]

theorem regime010_guard : facet002.determinant facet009 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet009 3).quartic.BernsteinNonnegCheck (1/2) (2973/4096) ∧
    (wallDualSecondPolynomial facet002 facet009 3).quartic.BernsteinNonnegCheck (1/2) (2973/4096) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009]

theorem regime010_point007_margin0 : (wallDualMargin facet002 facet009 3 ownedP007).BernsteinPosCheck (1/2) (2973/4096) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009, ownedP007]

theorem regime010_point007 : WallDualCheck facet002 facet009 3 ownedP007 (1/2) (2973/4096) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point007_margin0⟩

theorem regime010_point005_dominance : WallProjectionCheck 3 ownedP007 ownedP005 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP005]

theorem regime010_point006_dominance : WallProjectionCheck 3 ownedP007 ownedP006 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime010_point007_dominance : WallProjectionCheck 3 ownedP007 ownedP007 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime010_point009_dominance : WallProjectionCheck 3 ownedP007 ownedP009 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime010_point010_dominance : WallProjectionCheck 3 ownedP007 ownedP010 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP010]

theorem regime010_mirror15_005_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_005 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_005]

theorem regime010_mirror15_007_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_007 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_007]

theorem regime010_mirror15_008_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_008 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_008]

theorem regime010_mirror15_009_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_009 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_009]

theorem regime010_mirror15_010_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_010 (1/2) (2973/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_010]

theorem regime010_checked : regime010.Check 0 3 points (1/2) (2973/4096) := by
  unfold regime010 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet009_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime010_point007
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime010_point005_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_point007_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_point010_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror15_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror15_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror15_008_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror15_009_dominance⟩
    · exact ⟨ownedP007, by simp, regime010_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
