import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime010 : AnchoredWallDirectionCertificate := .ordinary facet010 facet015 [mirrorP12_009]

theorem regime010_guard : facet010.determinant facet015 ≠ 0 ∧
    (wallDualFirstPolynomial facet010 facet015 2).quartic.BernsteinNonnegCheck (7/16) (1755/2048) ∧
    (wallDualSecondPolynomial facet010 facet015 2).quartic.BernsteinNonnegCheck (7/16) (1755/2048) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015]

theorem regime010_mirror12_009_margin0 : (wallDualMargin facet010 facet015 2 mirrorP12_009).BernsteinPosCheck (7/16) (1755/2048) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet015, mirrorP12_009]

theorem regime010_mirror12_009 : WallDualCheck facet010 facet015 2 mirrorP12_009 (7/16) (1755/2048) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_mirror12_009_margin0⟩

theorem regime010_point005_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP005 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP005]

theorem regime010_point006_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP006 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP006]

theorem regime010_point007_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP007 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP007]

theorem regime010_point008_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP008 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP008]

theorem regime010_point009_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP009 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP009]

theorem regime010_point010_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP010 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP010]

theorem regime010_point011_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP011 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP011]

theorem regime010_mirror12_005_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_005 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_005]

theorem regime010_mirror12_006_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_006 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_006]

theorem regime010_mirror12_007_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_007 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_007]

theorem regime010_mirror12_008_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_008 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_008]

theorem regime010_mirror12_009_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_009 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_009]

theorem regime010_mirror12_010_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_010 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_010]

theorem regime010_mirror12_011_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_011 (7/16) (1755/2048) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_011]

theorem regime010_checked : regime010.Check 3 2 points (7/16) (1755/2048) := by
  unfold regime010 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet015_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime010_mirror12_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP12_009, by simp, regime010_point005_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_point006_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_point007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_point008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_point009_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_point010_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_point011_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_mirror12_005_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_mirror12_006_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_mirror12_007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_mirror12_008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_mirror12_009_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_mirror12_010_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime010_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
