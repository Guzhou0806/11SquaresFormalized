import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime011 : AnchoredWallDirectionCertificate := .crossing facet015 facet010 facet002 (857620617/1812031250) [mirrorP12_009]

theorem regime011_guard : facet015.determinant facet010 ≠ 0 ∧
    facet010.determinant facet002 ≠ 0 ∧
    0 < (857620617/1812031250:ℚ) ∧
    wallDualSecondPolynomial facet010 facet002 2 = (wallDualFirstPolynomial facet015 facet010 2).negScale (857620617/1812031250) ∧
    (wallDualSecondPolynomial facet015 facet010 2).quartic.BernsteinNonnegCheck (1755/2048) (1) ∧
    (wallDualFirstPolynomial facet010 facet002 2).quartic.BernsteinNonnegCheck (1755/2048) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet015, facet010, facet002]

theorem regime011_mirror12_009_margin0 : (wallDualMargin facet015 facet010 2 mirrorP12_009).BernsteinPosCheck (1755/2048) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet015, facet010, facet002, mirrorP12_009]

theorem regime011_mirror12_009_margin1 : (wallDualMargin facet010 facet002 2 mirrorP12_009).BernsteinPosCheck (1755/2048) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet015, facet010, facet002, mirrorP12_009]

theorem regime011_mirror12_009 : WallDualCrossingCheck facet015 facet010 facet002 2 mirrorP12_009 (1755/2048) (1) (857620617/1812031250) := by
  rcases regime011_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime011_mirror12_009_margin0, regime011_mirror12_009_margin1⟩

theorem regime011_point005_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP005 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP005]

theorem regime011_point006_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP006 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP006]

theorem regime011_point007_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP007 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP007]

theorem regime011_point008_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP008 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP008]

theorem regime011_point009_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP009 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP009]

theorem regime011_point010_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP010 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP010]

theorem regime011_point011_dominance : WallProjectionCheck 2 mirrorP12_009 ownedP011 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP011]

theorem regime011_mirror12_005_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_005 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_005]

theorem regime011_mirror12_006_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_006 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_006]

theorem regime011_mirror12_007_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_007 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_007]

theorem regime011_mirror12_008_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_008 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_008]

theorem regime011_mirror12_009_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_009 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_009]

theorem regime011_mirror12_010_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_010 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_010]

theorem regime011_mirror12_011_dominance : WallProjectionCheck 2 mirrorP12_009 mirrorP12_011 (1755/2048) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_011]

theorem regime011_checked : regime011.Check 3 2 points (1755/2048) (1) := by
  unfold regime011 AnchoredWallDirectionCertificate.Check
  refine ⟨facet015_mem, facet010_mem, facet002_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime011_mirror12_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP12_009, by simp, regime011_point005_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_point006_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_point007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_point008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_point009_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_point010_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_point011_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_mirror12_005_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_mirror12_006_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_mirror12_007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_mirror12_008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_mirror12_009_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_mirror12_010_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime011_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
