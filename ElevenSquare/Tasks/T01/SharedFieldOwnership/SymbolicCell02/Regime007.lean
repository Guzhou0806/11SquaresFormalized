import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime007 : AnchoredWallDirectionCertificate := .crossing facet014 facet013 facet009 (146115791345/139669658299) [ownedP005, ownedP009, mirrorP13_007, mirrorP13_010]

theorem regime007_guard : facet014.determinant facet013 ≠ 0 ∧
    facet013.determinant facet009 ≠ 0 ∧
    0 < (146115791345/139669658299:ℚ) ∧
    wallDualSecondPolynomial facet013 facet009 2 = (wallDualFirstPolynomial facet014 facet013 2).negScale (146115791345/139669658299) ∧
    (wallDualSecondPolynomial facet014 facet013 2).quartic.BernsteinNonnegCheck (0) (7/8) ∧
    (wallDualFirstPolynomial facet013 facet009 2).quartic.BernsteinNonnegCheck (0) (7/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009]

theorem regime007_point005_margin0 : (wallDualMargin facet014 facet013 2 ownedP005).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, ownedP005]

theorem regime007_point005_margin1 : (wallDualMargin facet013 facet009 2 ownedP005).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, ownedP005]

theorem regime007_point005 : WallDualCrossingCheck facet014 facet013 facet009 2 ownedP005 (0) (7/8) (146115791345/139669658299) := by
  rcases regime007_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime007_point005_margin0, regime007_point005_margin1⟩

theorem regime007_point009_margin0 : (wallDualMargin facet014 facet013 2 ownedP009).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, ownedP009]

theorem regime007_point009_margin1 : (wallDualMargin facet013 facet009 2 ownedP009).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, ownedP009]

theorem regime007_point009 : WallDualCrossingCheck facet014 facet013 facet009 2 ownedP009 (0) (7/8) (146115791345/139669658299) := by
  rcases regime007_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime007_point009_margin0, regime007_point009_margin1⟩

theorem regime007_mirror13_007_margin0 : (wallDualMargin facet014 facet013 2 mirrorP13_007).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, mirrorP13_007]

theorem regime007_mirror13_007_margin1 : (wallDualMargin facet013 facet009 2 mirrorP13_007).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, mirrorP13_007]

theorem regime007_mirror13_007 : WallDualCrossingCheck facet014 facet013 facet009 2 mirrorP13_007 (0) (7/8) (146115791345/139669658299) := by
  rcases regime007_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime007_mirror13_007_margin0, regime007_mirror13_007_margin1⟩

theorem regime007_mirror13_010_margin0 : (wallDualMargin facet014 facet013 2 mirrorP13_010).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, mirrorP13_010]

theorem regime007_mirror13_010_margin1 : (wallDualMargin facet013 facet009 2 mirrorP13_010).BernsteinPosCheck (0) (7/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet013, facet009, mirrorP13_010]

theorem regime007_mirror13_010 : WallDualCrossingCheck facet014 facet013 facet009 2 mirrorP13_010 (0) (7/8) (146115791345/139669658299) := by
  rcases regime007_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime007_mirror13_010_margin0, regime007_mirror13_010_margin1⟩

theorem regime007_point005_dominance : WallProjectionCheck 2 ownedP005 ownedP005 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP005]

theorem regime007_point006_dominance : WallProjectionCheck 2 ownedP005 ownedP006 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP006]

theorem regime007_point007_dominance : WallProjectionCheck 2 ownedP009 ownedP007 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime007_point008_dominance : WallProjectionCheck 2 ownedP009 ownedP008 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP008]

theorem regime007_point009_dominance : WallProjectionCheck 2 ownedP009 ownedP009 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime007_mirror13_005_dominance : WallProjectionCheck 2 ownedP009 mirrorP13_005 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_005]

theorem regime007_mirror13_006_dominance : WallProjectionCheck 2 ownedP009 mirrorP13_006 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_006]

theorem regime007_mirror13_007_dominance : WallProjectionCheck 2 mirrorP13_007 mirrorP13_007 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_007, mirrorP13_007]

theorem regime007_mirror13_010_dominance : WallProjectionCheck 2 mirrorP13_010 mirrorP13_010 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_010]

theorem regime007_mirror13_011_dominance : WallProjectionCheck 2 ownedP005 mirrorP13_011 (0) (7/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP13_011]

theorem regime007_checked : regime007.Check 2 2 points (0) (7/8) := by
  unfold regime007 AnchoredWallDirectionCertificate.Check
  refine ⟨facet014_mem, facet013_mem, facet009_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact regime007_point005
    · exact regime007_point009
    · exact regime007_mirror13_007
    · exact regime007_mirror13_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP005, by simp, regime007_point005_dominance⟩
    · exact ⟨ownedP005, by simp, regime007_point006_dominance⟩
    · exact ⟨ownedP009, by simp, regime007_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime007_point008_dominance⟩
    · exact ⟨ownedP009, by simp, regime007_point009_dominance⟩
    · exact ⟨ownedP009, by simp, regime007_mirror13_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime007_mirror13_006_dominance⟩
    · exact ⟨mirrorP13_007, by simp, regime007_mirror13_007_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime007_mirror13_010_dominance⟩
    · exact ⟨ownedP005, by simp, regime007_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
