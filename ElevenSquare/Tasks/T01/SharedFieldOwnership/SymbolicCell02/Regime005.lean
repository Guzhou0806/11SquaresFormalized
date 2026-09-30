import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime005 : AnchoredWallDirectionCertificate := .crossing facet013 facet009 facet002 (139669658299/260419500000) [mirrorP13_010]

theorem regime005_guard : facet013.determinant facet009 ≠ 0 ∧
    facet009.determinant facet002 ≠ 0 ∧
    0 < (139669658299/260419500000:ℚ) ∧
    wallDualSecondPolynomial facet009 facet002 1 = (wallDualFirstPolynomial facet013 facet009 1).negScale (139669658299/260419500000) ∧
    (wallDualSecondPolynomial facet013 facet009 1).quartic.BernsteinNonnegCheck (711/4096) (1/2) ∧
    (wallDualFirstPolynomial facet009 facet002 1).quartic.BernsteinNonnegCheck (711/4096) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet009, facet002]

theorem regime005_mirror13_010_margin0 : (wallDualMargin facet013 facet009 1 mirrorP13_010).BernsteinPosCheck (711/4096) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet009, facet002, mirrorP13_010]

theorem regime005_mirror13_010_margin1 : (wallDualMargin facet009 facet002 1 mirrorP13_010).BernsteinPosCheck (711/4096) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet009, facet002, mirrorP13_010]

theorem regime005_mirror13_010 : WallDualCrossingCheck facet013 facet009 facet002 1 mirrorP13_010 (711/4096) (1/2) (139669658299/260419500000) := by
  rcases regime005_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime005_mirror13_010_margin0, regime005_mirror13_010_margin1⟩

theorem regime005_point005_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP005 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP005]

theorem regime005_point006_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP006 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP006]

theorem regime005_point007_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP007 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP007]

theorem regime005_point008_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP008 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP008]

theorem regime005_point009_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP009 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP009]

theorem regime005_mirror13_005_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_005 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_005]

theorem regime005_mirror13_006_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_006 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_006]

theorem regime005_mirror13_007_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_007 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_007]

theorem regime005_mirror13_010_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_010 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_010]

theorem regime005_mirror13_011_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_011 (711/4096) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_011]

theorem regime005_checked : regime005.Check 2 1 points (711/4096) (1/2) := by
  unfold regime005 AnchoredWallDirectionCertificate.Check
  refine ⟨facet013_mem, facet009_mem, facet002_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime005_mirror13_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP13_010, by simp, regime005_point005_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_point006_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_point007_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_point008_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_point009_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_mirror13_005_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_mirror13_006_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_mirror13_007_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_mirror13_010_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime005_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
