import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime000 : AnchoredWallDirectionCertificate := .ordinary facet013 facet017 [ownedP010]

theorem regime000_guard : facet013.determinant facet017 ≠ 0 ∧
    (wallDualFirstPolynomial facet013 facet017 0).quartic.BernsteinNonnegCheck (0) (5/32) ∧
    (wallDualSecondPolynomial facet013 facet017 0).quartic.BernsteinNonnegCheck (0) (5/32) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet017]

theorem regime000_point010_margin0 : (wallDualMargin facet013 facet017 0 ownedP010).BernsteinPosCheck (0) (5/32) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet017, ownedP010]

theorem regime000_point010 : WallDualCheck facet013 facet017 0 ownedP010 (0) (5/32) := by
  rcases regime000_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime000_point010_margin0⟩

theorem regime000_point005_dominance : WallProjectionCheck 0 ownedP010 ownedP005 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP005]

theorem regime000_point006_dominance : WallProjectionCheck 0 ownedP010 ownedP006 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP006]

theorem regime000_point007_dominance : WallProjectionCheck 0 ownedP010 ownedP007 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP007]

theorem regime000_point008_dominance : WallProjectionCheck 0 ownedP010 ownedP008 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP008]

theorem regime000_point010_dominance : WallProjectionCheck 0 ownedP010 ownedP010 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime000_point011_dominance : WallProjectionCheck 0 ownedP010 ownedP011 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP011]

theorem regime000_point012_dominance : WallProjectionCheck 0 ownedP010 ownedP012 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP012]

theorem regime000_mirror11_006_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_006 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_006]

theorem regime000_mirror11_007_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_007 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_007]

theorem regime000_mirror11_008_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_008 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_008]

theorem regime000_mirror11_009_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_009 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_009]

theorem regime000_mirror11_010_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_010 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_010]

theorem regime000_mirror11_011_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_011 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_011]

theorem regime000_mirror11_012_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_012 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_012]

theorem regime000_mirror11_013_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_013 (0) (5/32) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_013]

theorem regime000_checked : regime000.Check 4 0 points (0) (5/32) := by
  unfold regime000 AnchoredWallDirectionCertificate.Check
  refine ⟨facet013_mem, facet017_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime000_point010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP010, by simp, regime000_point005_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_point006_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_point007_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_point008_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_point010_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_point011_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_point012_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_006_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_008_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_009_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_010_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_011_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_012_dominance⟩
    · exact ⟨ownedP010, by simp, regime000_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
