import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime007 : AnchoredWallDirectionCertificate := .ordinary facet010 facet015 [ownedP010]

theorem regime007_guard : facet010.determinant facet015 ≠ 0 ∧
    (wallDualFirstPolynomial facet010 facet015 2).quartic.BernsteinNonnegCheck (1/8) (1/4) ∧
    (wallDualSecondPolynomial facet010 facet015 2).quartic.BernsteinNonnegCheck (1/8) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015]

theorem regime007_point010_margin0 : (wallDualMargin facet010 facet015 2 ownedP010).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015, ownedP010]

theorem regime007_point010 : WallDualCheck facet010 facet015 2 ownedP010 (1/8) (1/4) := by
  rcases regime007_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime007_point010_margin0⟩

theorem regime007_point005_dominance : WallProjectionCheck 2 ownedP010 ownedP005 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP005]

theorem regime007_point006_dominance : WallProjectionCheck 2 ownedP010 ownedP006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP006]

theorem regime007_point007_dominance : WallProjectionCheck 2 ownedP010 ownedP007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP007]

theorem regime007_point008_dominance : WallProjectionCheck 2 ownedP010 ownedP008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP008]

theorem regime007_point009_dominance : WallProjectionCheck 2 ownedP010 ownedP009 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP009]

theorem regime007_point010_dominance : WallProjectionCheck 2 ownedP010 ownedP010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime007_point011_dominance : WallProjectionCheck 2 ownedP010 ownedP011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP011]

theorem regime007_mirror12_005_dominance : WallProjectionCheck 2 ownedP010 mirrorP12_005 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_005]

theorem regime007_mirror12_006_dominance : WallProjectionCheck 2 ownedP010 mirrorP12_006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_006]

theorem regime007_mirror12_007_dominance : WallProjectionCheck 2 ownedP010 mirrorP12_007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_007]

theorem regime007_mirror12_008_dominance : WallProjectionCheck 2 ownedP010 mirrorP12_008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_008]

theorem regime007_mirror12_009_dominance : WallProjectionCheck 2 ownedP010 mirrorP12_009 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_009]

theorem regime007_mirror12_010_dominance : WallProjectionCheck 2 ownedP010 mirrorP12_010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_010]

theorem regime007_mirror12_011_dominance : WallProjectionCheck 2 ownedP010 mirrorP12_011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_011]

theorem regime007_checked : regime007.Check 3 2 points (1/8) (1/4) := by
  unfold regime007 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet015_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime007_point010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP010, by simp, regime007_point005_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_point006_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_point007_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_point008_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_point009_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_point010_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_point011_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_mirror12_005_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_mirror12_006_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_mirror12_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_mirror12_008_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_mirror12_009_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_mirror12_010_dominance⟩
    · exact ⟨ownedP010, by simp, regime007_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
