import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime009 : AnchoredWallDirectionCertificate := .ordinary facet000 facet016 [ownedP011]

theorem regime009_guard : facet000.determinant facet016 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet016 2).quartic.BernsteinNonnegCheck (0) (1/8) ∧
    (wallDualSecondPolynomial facet000 facet016 2).quartic.BernsteinNonnegCheck (0) (1/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016]

theorem regime009_point011_margin0 : (wallDualMargin facet000 facet016 2 ownedP011).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016, ownedP011]

theorem regime009_point011 : WallDualCheck facet000 facet016 2 ownedP011 (0) (1/8) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_point011_margin0⟩

theorem regime009_point005_dominance : WallProjectionCheck 2 ownedP011 ownedP005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP005]

theorem regime009_point006_dominance : WallProjectionCheck 2 ownedP011 ownedP006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP006]

theorem regime009_point007_dominance : WallProjectionCheck 2 ownedP011 ownedP007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP007]

theorem regime009_point008_dominance : WallProjectionCheck 2 ownedP011 ownedP008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP008]

theorem regime009_point010_dominance : WallProjectionCheck 2 ownedP011 ownedP010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP010]

theorem regime009_point011_dominance : WallProjectionCheck 2 ownedP011 ownedP011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime009_point012_dominance : WallProjectionCheck 2 ownedP011 ownedP012 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP012]

theorem regime009_mirror11_006_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_006]

theorem regime009_mirror11_007_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_007]

theorem regime009_mirror11_008_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_008]

theorem regime009_mirror11_009_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_009]

theorem regime009_mirror11_010_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_010]

theorem regime009_mirror11_011_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_011]

theorem regime009_mirror11_012_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_012 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_012]

theorem regime009_mirror11_013_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_013 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_013]

theorem regime009_checked : regime009.Check 4 2 points (0) (1/8) := by
  unfold regime009 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet016_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime009_point011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP011, by simp, regime009_point005_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_point006_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_point007_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_point008_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_point011_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_point012_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_006_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_007_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_008_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_009_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_010_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_011_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_012_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
