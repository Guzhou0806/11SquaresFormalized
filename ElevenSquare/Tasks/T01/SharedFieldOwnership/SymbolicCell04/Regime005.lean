import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime005 : AnchoredWallDirectionCertificate := .ordinary facet000 facet008 [mirrorP11_010]

theorem regime005_guard : facet000.determinant facet008 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (0) (1/2) ∧
    (wallDualSecondPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (0) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008]

theorem regime005_mirror11_010_margin0 : (wallDualMargin facet000 facet008 1 mirrorP11_010).BernsteinPosCheck (0) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, mirrorP11_010]

theorem regime005_mirror11_010 : WallDualCheck facet000 facet008 1 mirrorP11_010 (0) (1/2) := by
  rcases regime005_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime005_mirror11_010_margin0⟩

theorem regime005_point005_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP005]

theorem regime005_point006_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP006]

theorem regime005_point007_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP007]

theorem regime005_point008_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP008]

theorem regime005_point010_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP010]

theorem regime005_point011_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP011 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP011]

theorem regime005_point012_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP012 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP012]

theorem regime005_mirror11_006_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_006]

theorem regime005_mirror11_007_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_007]

theorem regime005_mirror11_008_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_008]

theorem regime005_mirror11_009_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_009 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_009]

theorem regime005_mirror11_010_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_010]

theorem regime005_mirror11_011_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_011 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_011]

theorem regime005_mirror11_012_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_012 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_012]

theorem regime005_mirror11_013_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_013 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_013]

theorem regime005_checked : regime005.Check 4 1 points (0) (1/2) := by
  unfold regime005 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime005_mirror11_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP11_010, by simp, regime005_point005_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_point006_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_point007_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_point008_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_point010_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_point011_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_point012_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_006_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_007_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_008_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_009_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_010_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_011_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_012_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime005_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
