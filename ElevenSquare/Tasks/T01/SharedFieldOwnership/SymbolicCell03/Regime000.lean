import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime000 : AnchoredWallDirectionCertificate := .ordinary facet001 facet015 [ownedP009]

theorem regime000_guard : facet001.determinant facet015 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet015 0).quartic.BernsteinNonnegCheck (0) (1/2) ∧
    (wallDualSecondPolynomial facet001 facet015 0).quartic.BernsteinNonnegCheck (0) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015]

theorem regime000_point009_margin0 : (wallDualMargin facet001 facet015 0 ownedP009).BernsteinPosCheck (0) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015, ownedP009]

theorem regime000_point009 : WallDualCheck facet001 facet015 0 ownedP009 (0) (1/2) := by
  rcases regime000_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime000_point009_margin0⟩

theorem regime000_point005_dominance : WallProjectionCheck 0 ownedP009 ownedP005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP005]

theorem regime000_point006_dominance : WallProjectionCheck 0 ownedP009 ownedP006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP006]

theorem regime000_point007_dominance : WallProjectionCheck 0 ownedP009 ownedP007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime000_point008_dominance : WallProjectionCheck 0 ownedP009 ownedP008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP008]

theorem regime000_point009_dominance : WallProjectionCheck 0 ownedP009 ownedP009 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime000_point010_dominance : WallProjectionCheck 0 ownedP009 ownedP010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP010]

theorem regime000_point011_dominance : WallProjectionCheck 0 ownedP009 ownedP011 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP011]

theorem regime000_mirror12_005_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_005]

theorem regime000_mirror12_006_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_006]

theorem regime000_mirror12_007_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_007]

theorem regime000_mirror12_008_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_008]

theorem regime000_mirror12_009_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_009 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_009]

theorem regime000_mirror12_010_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_010]

theorem regime000_mirror12_011_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_011 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_011]

theorem regime000_checked : regime000.Check 3 0 points (0) (1/2) := by
  unfold regime000 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet015_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime000_point009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP009, by simp, regime000_point005_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_point006_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_point008_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_point009_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_point010_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_point011_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_mirror12_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_mirror12_006_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_mirror12_007_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_mirror12_008_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_mirror12_009_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_mirror12_010_dominance⟩
    · exact ⟨ownedP009, by simp, regime000_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
