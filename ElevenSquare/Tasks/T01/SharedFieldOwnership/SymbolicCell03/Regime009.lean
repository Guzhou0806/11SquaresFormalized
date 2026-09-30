import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime009 : AnchoredWallDirectionCertificate := .ordinary facet010 facet015 [ownedP005, ownedP011, mirrorP12_008, mirrorP12_009]

theorem regime009_guard : facet010.determinant facet015 ≠ 0 ∧
    (wallDualFirstPolynomial facet010 facet015 2).quartic.BernsteinNonnegCheck (3/8) (7/16) ∧
    (wallDualSecondPolynomial facet010 facet015 2).quartic.BernsteinNonnegCheck (3/8) (7/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015]

theorem regime009_point005_margin0 : (wallDualMargin facet010 facet015 2 ownedP005).BernsteinPosCheck (3/8) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015, ownedP005]

theorem regime009_point005 : WallDualCheck facet010 facet015 2 ownedP005 (3/8) (7/16) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_point005_margin0⟩

theorem regime009_point011_margin0 : (wallDualMargin facet010 facet015 2 ownedP011).BernsteinPosCheck (3/8) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015, ownedP011]

theorem regime009_point011 : WallDualCheck facet010 facet015 2 ownedP011 (3/8) (7/16) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_point011_margin0⟩

theorem regime009_mirror12_008_margin0 : (wallDualMargin facet010 facet015 2 mirrorP12_008).BernsteinPosCheck (3/8) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015, mirrorP12_008]

theorem regime009_mirror12_008 : WallDualCheck facet010 facet015 2 mirrorP12_008 (3/8) (7/16) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_mirror12_008_margin0⟩

theorem regime009_mirror12_009_margin0 : (wallDualMargin facet010 facet015 2 mirrorP12_009).BernsteinPosCheck (3/8) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015, mirrorP12_009]

theorem regime009_mirror12_009 : WallDualCheck facet010 facet015 2 mirrorP12_009 (3/8) (7/16) := by
  rcases regime009_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime009_mirror12_009_margin0⟩

theorem regime009_point005_dominance : WallProjectionCheck 2 ownedP005 ownedP005 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP005]

theorem regime009_point006_dominance : WallProjectionCheck 2 ownedP005 ownedP006 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP006]

theorem regime009_point007_dominance : WallProjectionCheck 2 ownedP005 ownedP007 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP007]

theorem regime009_point008_dominance : WallProjectionCheck 2 ownedP005 ownedP008 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP008]

theorem regime009_point009_dominance : WallProjectionCheck 2 ownedP005 ownedP009 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP009]

theorem regime009_point010_dominance : WallProjectionCheck 2 ownedP005 ownedP010 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP010]

theorem regime009_point011_dominance : WallProjectionCheck 2 ownedP011 ownedP011 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime009_mirror12_005_dominance : WallProjectionCheck 2 ownedP005 mirrorP12_005 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP12_005]

theorem regime009_mirror12_006_dominance : WallProjectionCheck 2 ownedP005 mirrorP12_006 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP12_006]

theorem regime009_mirror12_007_dominance : WallProjectionCheck 2 ownedP005 mirrorP12_007 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP12_007]

theorem regime009_mirror12_008_dominance : WallProjectionCheck 2 mirrorP12_008 mirrorP12_008 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_008, mirrorP12_008]

theorem regime009_mirror12_009_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_009 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_009]

theorem regime009_mirror12_010_dominance : WallProjectionCheck 2 ownedP005 mirrorP12_010 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP12_010]

theorem regime009_mirror12_011_dominance : WallProjectionCheck 2 ownedP005 mirrorP12_011 (3/8) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP12_011]

theorem regime009_checked : regime009.Check 3 2 points (3/8) (7/16) := by
  unfold regime009 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet015_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact regime009_point005
    · exact regime009_point011
    · exact regime009_mirror12_008
    · exact regime009_mirror12_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP005, by simp, regime009_point005_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_point006_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_point007_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_point008_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_point009_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime009_point011_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_mirror12_005_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_mirror12_006_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_mirror12_007_dominance⟩
    · exact ⟨mirrorP12_008, by simp, regime009_mirror12_008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime009_mirror12_009_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_mirror12_010_dominance⟩
    · exact ⟨ownedP005, by simp, regime009_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
