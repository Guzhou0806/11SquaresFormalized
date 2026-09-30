import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime011 : AnchoredWallDirectionCertificate := .crossing facet019 facet014 facet010 (271974970539/284027168089) [ownedP006, ownedP013, mirrorP08_008, mirrorP08_010]

theorem regime011_guard : facet019.determinant facet014 ≠ 0 ∧
    facet014.determinant facet010 ≠ 0 ∧
    0 < (271974970539/284027168089:ℚ) ∧
    wallDualSecondPolynomial facet014 facet010 2 = (wallDualFirstPolynomial facet019 facet014 2).negScale (271974970539/284027168089) ∧
    (wallDualSecondPolynomial facet019 facet014 2).quartic.BernsteinNonnegCheck (1/4) (1) ∧
    (wallDualFirstPolynomial facet014 facet010 2).quartic.BernsteinNonnegCheck (1/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010]

theorem regime011_point006_margin0 : (wallDualMargin facet019 facet014 2 ownedP006).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, ownedP006]

theorem regime011_point006_margin1 : (wallDualMargin facet014 facet010 2 ownedP006).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, ownedP006]

theorem regime011_point006 : WallDualCrossingCheck facet019 facet014 facet010 2 ownedP006 (1/4) (1) (271974970539/284027168089) := by
  rcases regime011_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime011_point006_margin0, regime011_point006_margin1⟩

theorem regime011_point013_margin0 : (wallDualMargin facet019 facet014 2 ownedP013).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, ownedP013]

theorem regime011_point013_margin1 : (wallDualMargin facet014 facet010 2 ownedP013).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, ownedP013]

theorem regime011_point013 : WallDualCrossingCheck facet019 facet014 facet010 2 ownedP013 (1/4) (1) (271974970539/284027168089) := by
  rcases regime011_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime011_point013_margin0, regime011_point013_margin1⟩

theorem regime011_mirror08_008_margin0 : (wallDualMargin facet019 facet014 2 mirrorP08_008).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, mirrorP08_008]

theorem regime011_mirror08_008_margin1 : (wallDualMargin facet014 facet010 2 mirrorP08_008).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, mirrorP08_008]

theorem regime011_mirror08_008 : WallDualCrossingCheck facet019 facet014 facet010 2 mirrorP08_008 (1/4) (1) (271974970539/284027168089) := by
  rcases regime011_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime011_mirror08_008_margin0, regime011_mirror08_008_margin1⟩

theorem regime011_mirror08_010_margin0 : (wallDualMargin facet019 facet014 2 mirrorP08_010).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, mirrorP08_010]

theorem regime011_mirror08_010_margin1 : (wallDualMargin facet014 facet010 2 mirrorP08_010).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet019, facet014, facet010, mirrorP08_010]

theorem regime011_mirror08_010 : WallDualCrossingCheck facet019 facet014 facet010 2 mirrorP08_010 (1/4) (1) (271974970539/284027168089) := by
  rcases regime011_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime011_mirror08_010_margin0, regime011_mirror08_010_margin1⟩

theorem regime011_point006_dominance : WallProjectionCheck 2 ownedP006 ownedP006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP006]

theorem regime011_point007_dominance : WallProjectionCheck 2 ownedP006 ownedP007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP007]

theorem regime011_point008_dominance : WallProjectionCheck 2 ownedP006 ownedP008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP008]

theorem regime011_point009_dominance : WallProjectionCheck 2 ownedP006 ownedP009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP009]

theorem regime011_point010_dominance : WallProjectionCheck 2 ownedP006 ownedP010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP010]

theorem regime011_point011_dominance : WallProjectionCheck 2 ownedP006 ownedP011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP011]

theorem regime011_point012_dominance : WallProjectionCheck 2 ownedP013 ownedP012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP012]

theorem regime011_point013_dominance : WallProjectionCheck 2 ownedP013 ownedP013 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP013]

theorem regime011_point014_dominance : WallProjectionCheck 2 ownedP006 ownedP014 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP014]

theorem regime011_mirror08_005_dominance : WallProjectionCheck 2 ownedP006 mirrorP08_005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP08_005]

theorem regime011_mirror08_006_dominance : WallProjectionCheck 2 ownedP006 mirrorP08_006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP08_006]

theorem regime011_mirror08_007_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_007]

theorem regime011_mirror08_008_dominance : WallProjectionCheck 2 mirrorP08_008 mirrorP08_008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_008, mirrorP08_008]

theorem regime011_mirror08_010_dominance : WallProjectionCheck 2 mirrorP08_010 mirrorP08_010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_010, mirrorP08_010]

theorem regime011_mirror08_011_dominance : WallProjectionCheck 2 ownedP006 mirrorP08_011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP08_011]

theorem regime011_mirror08_012_dominance : WallProjectionCheck 2 ownedP006 mirrorP08_012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP08_012]

theorem regime011_mirror08_013_dominance : WallProjectionCheck 2 ownedP006 mirrorP08_013 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP08_013]

theorem regime011_checked : regime011.Check 7 2 points (1/4) (1) := by
  unfold regime011 AnchoredWallDirectionCertificate.Check
  refine ⟨facet019_mem, facet014_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact regime011_point006
    · exact regime011_point013
    · exact regime011_mirror08_008
    · exact regime011_mirror08_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP006, by simp, regime011_point006_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_point007_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_point008_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_point009_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_point010_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_point011_dominance⟩
    · exact ⟨ownedP013, by simp, regime011_point012_dominance⟩
    · exact ⟨ownedP013, by simp, regime011_point013_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_point014_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_mirror08_005_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_mirror08_006_dominance⟩
    · exact ⟨ownedP013, by simp, regime011_mirror08_007_dominance⟩
    · exact ⟨mirrorP08_008, by simp, regime011_mirror08_008_dominance⟩
    · exact ⟨mirrorP08_010, by simp, regime011_mirror08_010_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_mirror08_011_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_mirror08_012_dominance⟩
    · exact ⟨ownedP006, by simp, regime011_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
