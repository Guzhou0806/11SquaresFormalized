import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime003 : AnchoredWallDirectionCertificate := .crossing facet001 facet019 facet008 (105638000000/165061440103) [ownedP013]

theorem regime003_guard : facet001.determinant facet019 ≠ 0 ∧
    facet019.determinant facet008 ≠ 0 ∧
    0 < (105638000000/165061440103:ℚ) ∧
    wallDualSecondPolynomial facet019 facet008 0 = (wallDualFirstPolynomial facet001 facet019 0).negScale (105638000000/165061440103) ∧
    (wallDualSecondPolynomial facet001 facet019 0).quartic.BernsteinNonnegCheck (3/4) (1) ∧
    (wallDualFirstPolynomial facet019 facet008 0).quartic.BernsteinNonnegCheck (3/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, facet008]

theorem regime003_point013_margin0 : (wallDualMargin facet001 facet019 0 ownedP013).BernsteinPosCheck (3/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, facet008, ownedP013]

theorem regime003_point013_margin1 : (wallDualMargin facet019 facet008 0 ownedP013).BernsteinPosCheck (3/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, facet008, ownedP013]

theorem regime003_point013 : WallDualCrossingCheck facet001 facet019 facet008 0 ownedP013 (3/4) (1) (105638000000/165061440103) := by
  rcases regime003_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime003_point013_margin0, regime003_point013_margin1⟩

theorem regime003_point006_dominance : WallProjectionCheck 0 ownedP013 ownedP006 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP006]

theorem regime003_point007_dominance : WallProjectionCheck 0 ownedP013 ownedP007 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP007]

theorem regime003_point008_dominance : WallProjectionCheck 0 ownedP013 ownedP008 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP008]

theorem regime003_point009_dominance : WallProjectionCheck 0 ownedP013 ownedP009 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP009]

theorem regime003_point010_dominance : WallProjectionCheck 0 ownedP013 ownedP010 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP010]

theorem regime003_point011_dominance : WallProjectionCheck 0 ownedP013 ownedP011 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP011]

theorem regime003_point012_dominance : WallProjectionCheck 0 ownedP013 ownedP012 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP012]

theorem regime003_point013_dominance : WallProjectionCheck 0 ownedP013 ownedP013 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP013]

theorem regime003_point014_dominance : WallProjectionCheck 0 ownedP013 ownedP014 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP014]

theorem regime003_mirror08_005_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_005 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_005]

theorem regime003_mirror08_006_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_006 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_006]

theorem regime003_mirror08_007_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_007 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_007]

theorem regime003_mirror08_008_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_008 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_008]

theorem regime003_mirror08_010_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_010 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_010]

theorem regime003_mirror08_011_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_011 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_011]

theorem regime003_mirror08_012_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_012 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_012]

theorem regime003_mirror08_013_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_013 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_013]

theorem regime003_checked : regime003.Check 7 0 points (3/4) (1) := by
  unfold regime003 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet019_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime003_point013
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP013, by simp, regime003_point006_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point007_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point008_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point009_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point010_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point011_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point012_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point013_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_point014_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_005_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_006_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_007_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_008_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_010_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_011_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_012_dominance⟩
    · exact ⟨ownedP013, by simp, regime003_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
