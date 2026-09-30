import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime006 : AnchoredWallDirectionCertificate := .ordinary facet002 facet009 [mirrorP13_010]

theorem regime006_guard : facet002.determinant facet009 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet009 1).quartic.BernsteinNonnegCheck (1/2) (1) ∧
    (wallDualSecondPolynomial facet002 facet009 1).quartic.BernsteinNonnegCheck (1/2) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009]

theorem regime006_mirror13_010_margin0 : (wallDualMargin facet002 facet009 1 mirrorP13_010).BernsteinPosCheck (1/2) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009, mirrorP13_010]

theorem regime006_mirror13_010 : WallDualCheck facet002 facet009 1 mirrorP13_010 (1/2) (1) := by
  rcases regime006_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime006_mirror13_010_margin0⟩

theorem regime006_point005_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP005 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP005]

theorem regime006_point006_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP006]

theorem regime006_point007_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP007 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP007]

theorem regime006_point008_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP008 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP008]

theorem regime006_point009_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP009 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP009]

theorem regime006_mirror13_005_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_005 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_005]

theorem regime006_mirror13_006_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_006]

theorem regime006_mirror13_007_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_007 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_007]

theorem regime006_mirror13_010_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_010 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_010]

theorem regime006_mirror13_011_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_011 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_011]

theorem regime006_checked : regime006.Check 2 1 points (1/2) (1) := by
  unfold regime006 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet009_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime006_mirror13_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP13_010, by simp, regime006_point005_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_point006_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_point007_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_point008_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_point009_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_mirror13_005_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_mirror13_006_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_mirror13_007_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_mirror13_010_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime006_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
