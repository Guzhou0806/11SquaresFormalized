import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime004 : AnchoredWallDirectionCertificate := .ordinary facet000 facet002 [mirrorP15_010]

theorem regime004_guard : facet000.determinant facet002 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet002 1).quartic.BernsteinNonnegCheck (0) (1) ∧
    (wallDualSecondPolynomial facet000 facet002 1).quartic.BernsteinNonnegCheck (0) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet002]

theorem regime004_mirror15_010_margin0 : (wallDualMargin facet000 facet002 1 mirrorP15_010).BernsteinPosCheck (0) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet002, mirrorP15_010]

theorem regime004_mirror15_010 : WallDualCheck facet000 facet002 1 mirrorP15_010 (0) (1) := by
  rcases regime004_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime004_mirror15_010_margin0⟩

theorem regime004_point005_dominance : WallProjectionCheck 1 mirrorP15_010 ownedP005 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, ownedP005]

theorem regime004_point006_dominance : WallProjectionCheck 1 mirrorP15_010 ownedP006 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, ownedP006]

theorem regime004_point007_dominance : WallProjectionCheck 1 mirrorP15_010 ownedP007 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, ownedP007]

theorem regime004_point009_dominance : WallProjectionCheck 1 mirrorP15_010 ownedP009 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, ownedP009]

theorem regime004_point010_dominance : WallProjectionCheck 1 mirrorP15_010 ownedP010 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, ownedP010]

theorem regime004_mirror15_005_dominance : WallProjectionCheck 1 mirrorP15_010 mirrorP15_005 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, mirrorP15_005]

theorem regime004_mirror15_007_dominance : WallProjectionCheck 1 mirrorP15_010 mirrorP15_007 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, mirrorP15_007]

theorem regime004_mirror15_008_dominance : WallProjectionCheck 1 mirrorP15_010 mirrorP15_008 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, mirrorP15_008]

theorem regime004_mirror15_009_dominance : WallProjectionCheck 1 mirrorP15_010 mirrorP15_009 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, mirrorP15_009]

theorem regime004_mirror15_010_dominance : WallProjectionCheck 1 mirrorP15_010 mirrorP15_010 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_010, mirrorP15_010]

theorem regime004_checked : regime004.Check 0 1 points (0) (1) := by
  unfold regime004 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet002_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime004_mirror15_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP15_010, by simp, regime004_point005_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_point006_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_point007_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_point009_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_point010_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_mirror15_005_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_mirror15_007_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_mirror15_008_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_mirror15_009_dominance⟩
    · exact ⟨mirrorP15_010, by simp, regime004_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
