import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime014 : AnchoredWallDirectionCertificate := .crossing facet008 facet013 facet017 (2073350951/2089762215) [ownedP010, mirrorP11_006, mirrorP11_012]

theorem regime014_guard : facet008.determinant facet013 ≠ 0 ∧
    facet013.determinant facet017 ≠ 0 ∧
    0 < (2073350951/2089762215:ℚ) ∧
    wallDualSecondPolynomial facet013 facet017 3 = (wallDualFirstPolynomial facet008 facet013 3).negScale (2073350951/2089762215) ∧
    (wallDualSecondPolynomial facet008 facet013 3).quartic.BernsteinNonnegCheck (1/4) (1) ∧
    (wallDualFirstPolynomial facet013 facet017 3).quartic.BernsteinNonnegCheck (1/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, facet017]

theorem regime014_point010_margin0 : (wallDualMargin facet008 facet013 3 ownedP010).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, facet017, ownedP010]

theorem regime014_point010_margin1 : (wallDualMargin facet013 facet017 3 ownedP010).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, facet017, ownedP010]

theorem regime014_point010 : WallDualCrossingCheck facet008 facet013 facet017 3 ownedP010 (1/4) (1) (2073350951/2089762215) := by
  rcases regime014_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime014_point010_margin0, regime014_point010_margin1⟩

theorem regime014_mirror11_006_margin0 : (wallDualMargin facet008 facet013 3 mirrorP11_006).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, facet017, mirrorP11_006]

theorem regime014_mirror11_006_margin1 : (wallDualMargin facet013 facet017 3 mirrorP11_006).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, facet017, mirrorP11_006]

theorem regime014_mirror11_006 : WallDualCrossingCheck facet008 facet013 facet017 3 mirrorP11_006 (1/4) (1) (2073350951/2089762215) := by
  rcases regime014_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime014_mirror11_006_margin0, regime014_mirror11_006_margin1⟩

theorem regime014_mirror11_012_margin0 : (wallDualMargin facet008 facet013 3 mirrorP11_012).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, facet017, mirrorP11_012]

theorem regime014_mirror11_012_margin1 : (wallDualMargin facet013 facet017 3 mirrorP11_012).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, facet017, mirrorP11_012]

theorem regime014_mirror11_012 : WallDualCrossingCheck facet008 facet013 facet017 3 mirrorP11_012 (1/4) (1) (2073350951/2089762215) := by
  rcases regime014_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime014_mirror11_012_margin0, regime014_mirror11_012_margin1⟩

theorem regime014_point005_dominance : WallProjectionCheck 3 ownedP010 ownedP005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP005]

theorem regime014_point006_dominance : WallProjectionCheck 3 ownedP010 ownedP006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP006]

theorem regime014_point007_dominance : WallProjectionCheck 3 ownedP010 ownedP007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP007]

theorem regime014_point008_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP008]

theorem regime014_point010_dominance : WallProjectionCheck 3 ownedP010 ownedP010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime014_point011_dominance : WallProjectionCheck 3 ownedP010 ownedP011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP011]

theorem regime014_point012_dominance : WallProjectionCheck 3 ownedP010 ownedP012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP012]

theorem regime014_mirror11_006_dominance : WallProjectionCheck 3 mirrorP11_006 mirrorP11_006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_006, mirrorP11_006]

theorem regime014_mirror11_007_dominance : WallProjectionCheck 3 ownedP010 mirrorP11_007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_007]

theorem regime014_mirror11_008_dominance : WallProjectionCheck 3 ownedP010 mirrorP11_008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_008]

theorem regime014_mirror11_009_dominance : WallProjectionCheck 3 ownedP010 mirrorP11_009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_009]

theorem regime014_mirror11_010_dominance : WallProjectionCheck 3 ownedP010 mirrorP11_010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_010]

theorem regime014_mirror11_011_dominance : WallProjectionCheck 3 ownedP010 mirrorP11_011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_011]

theorem regime014_mirror11_012_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_012]

theorem regime014_mirror11_013_dominance : WallProjectionCheck 3 ownedP010 mirrorP11_013 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_013]

theorem regime014_checked : regime014.Check 4 3 points (1/4) (1) := by
  unfold regime014 AnchoredWallDirectionCertificate.Check
  refine ⟨facet008_mem, facet013_mem, facet017_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact regime014_point010
    · exact regime014_mirror11_006
    · exact regime014_mirror11_012
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP010, by simp, regime014_point005_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_point006_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_point007_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime014_point008_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_point010_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_point011_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_point012_dominance⟩
    · exact ⟨mirrorP11_006, by simp, regime014_mirror11_006_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_mirror11_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_mirror11_008_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_mirror11_009_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_mirror11_010_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_mirror11_011_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime014_mirror11_012_dominance⟩
    · exact ⟨ownedP010, by simp, regime014_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
