import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime005 : AnchoredWallDirectionCertificate := .ordinary facet002 facet010 [mirrorP12_011]

theorem regime005_guard : facet002.determinant facet010 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet010 1).quartic.BernsteinNonnegCheck (1/4) (1) ∧
    (wallDualSecondPolynomial facet002 facet010 1).quartic.BernsteinNonnegCheck (1/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010]

theorem regime005_mirror12_011_margin0 : (wallDualMargin facet002 facet010 1 mirrorP12_011).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, mirrorP12_011]

theorem regime005_mirror12_011 : WallDualCheck facet002 facet010 1 mirrorP12_011 (1/4) (1) := by
  rcases regime005_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime005_mirror12_011_margin0⟩

theorem regime005_point005_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP005]

theorem regime005_point006_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP006]

theorem regime005_point007_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP007]

theorem regime005_point008_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP008]

theorem regime005_point009_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP009]

theorem regime005_point010_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP010]

theorem regime005_point011_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP011]

theorem regime005_mirror12_005_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_005]

theorem regime005_mirror12_006_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_006]

theorem regime005_mirror12_007_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_007]

theorem regime005_mirror12_008_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_008]

theorem regime005_mirror12_009_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_009]

theorem regime005_mirror12_010_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_010]

theorem regime005_mirror12_011_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_011]

theorem regime005_checked : regime005.Check 3 1 points (1/4) (1) := by
  unfold regime005 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime005_mirror12_011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP12_011, by simp, regime005_point005_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_point006_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_point007_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_point008_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_point009_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_point010_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_point011_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_mirror12_005_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_mirror12_006_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_mirror12_007_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_mirror12_008_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_mirror12_009_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_mirror12_010_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime005_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
