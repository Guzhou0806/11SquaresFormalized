import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime005 : AnchoredWallDirectionCertificate := .crossing facet001 facet013 facet008 (534860000000/286195087637) [ownedP005, ownedP008]

theorem regime005_guard : facet001.determinant facet013 ≠ 0 ∧
    facet013.determinant facet008 ≠ 0 ∧
    0 < (534860000000/286195087637:ℚ) ∧
    wallDualSecondPolynomial facet013 facet008 2 = (wallDualFirstPolynomial facet001 facet013 2).negScale (534860000000/286195087637) ∧
    (wallDualSecondPolynomial facet001 facet013 2).quartic.BernsteinNonnegCheck (0) (3/8) ∧
    (wallDualFirstPolynomial facet013 facet008 2).quartic.BernsteinNonnegCheck (0) (3/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet013, facet008]

theorem regime005_point005_margin0 : (wallDualMargin facet001 facet013 2 ownedP005).BernsteinPosCheck (0) (3/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet013, facet008, ownedP005]

theorem regime005_point005_margin1 : (wallDualMargin facet013 facet008 2 ownedP005).BernsteinPosCheck (0) (3/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet013, facet008, ownedP005]

theorem regime005_point005 : WallDualCrossingCheck facet001 facet013 facet008 2 ownedP005 (0) (3/8) (534860000000/286195087637) := by
  rcases regime005_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime005_point005_margin0, regime005_point005_margin1⟩

theorem regime005_point008_margin0 : (wallDualMargin facet001 facet013 2 ownedP008).BernsteinPosCheck (0) (3/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet013, facet008, ownedP008]

theorem regime005_point008_margin1 : (wallDualMargin facet013 facet008 2 ownedP008).BernsteinPosCheck (0) (3/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet013, facet008, ownedP008]

theorem regime005_point008 : WallDualCrossingCheck facet001 facet013 facet008 2 ownedP008 (0) (3/8) (534860000000/286195087637) := by
  rcases regime005_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime005_point008_margin0, regime005_point008_margin1⟩

theorem regime005_point005_dominance : WallProjectionCheck 2 ownedP005 ownedP005 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP005]

theorem regime005_point006_dominance : WallProjectionCheck 2 ownedP005 ownedP006 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP006]

theorem regime005_point007_dominance : WallProjectionCheck 2 ownedP005 ownedP007 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP007]

theorem regime005_point008_dominance : WallProjectionCheck 2 ownedP008 ownedP008 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime005_mirror14_005_dominance : WallProjectionCheck 2 ownedP005 mirrorP14_005 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP14_005]

theorem regime005_mirror14_006_dominance : WallProjectionCheck 2 ownedP008 mirrorP14_006 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_006]

theorem regime005_mirror14_008_dominance : WallProjectionCheck 2 ownedP005 mirrorP14_008 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP14_008]

theorem regime005_mirror14_009_dominance : WallProjectionCheck 2 ownedP005 mirrorP14_009 (0) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP14_009]

theorem regime005_checked : regime005.Check 1 2 points (0) (3/8) := by
  unfold regime005 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet013_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime005_point005
    · exact regime005_point008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP005, by simp, regime005_point005_dominance⟩
    · exact ⟨ownedP005, by simp, regime005_point006_dominance⟩
    · exact ⟨ownedP005, by simp, regime005_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime005_point008_dominance⟩
    · exact ⟨ownedP005, by simp, regime005_mirror14_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime005_mirror14_006_dominance⟩
    · exact ⟨ownedP005, by simp, regime005_mirror14_008_dominance⟩
    · exact ⟨ownedP005, by simp, regime005_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
