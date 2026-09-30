import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime001 : AnchoredWallDirectionCertificate := .crossing facet009 facet013 facet012 (286195087637/286122431238) [ownedP007, ownedP009]

theorem regime001_guard : facet009.determinant facet013 ≠ 0 ∧
    facet013.determinant facet012 ≠ 0 ∧
    0 < (286195087637/286122431238:ℚ) ∧
    wallDualSecondPolynomial facet013 facet012 0 = (wallDualFirstPolynomial facet009 facet013 0).negScale (286195087637/286122431238) ∧
    (wallDualSecondPolynomial facet009 facet013 0).quartic.BernsteinNonnegCheck (1/16) (1/2) ∧
    (wallDualFirstPolynomial facet013 facet012 0).quartic.BernsteinNonnegCheck (1/16) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013, facet012]

theorem regime001_point007_margin0 : (wallDualMargin facet009 facet013 0 ownedP007).BernsteinPosCheck (1/16) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013, facet012, ownedP007]

theorem regime001_point007_margin1 : (wallDualMargin facet013 facet012 0 ownedP007).BernsteinPosCheck (1/16) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013, facet012, ownedP007]

theorem regime001_point007 : WallDualCrossingCheck facet009 facet013 facet012 0 ownedP007 (1/16) (1/2) (286195087637/286122431238) := by
  rcases regime001_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime001_point007_margin0, regime001_point007_margin1⟩

theorem regime001_point009_margin0 : (wallDualMargin facet009 facet013 0 ownedP009).BernsteinPosCheck (1/16) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013, facet012, ownedP009]

theorem regime001_point009_margin1 : (wallDualMargin facet013 facet012 0 ownedP009).BernsteinPosCheck (1/16) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013, facet012, ownedP009]

theorem regime001_point009 : WallDualCrossingCheck facet009 facet013 facet012 0 ownedP009 (1/16) (1/2) (286195087637/286122431238) := by
  rcases regime001_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime001_point009_margin0, regime001_point009_margin1⟩

theorem regime001_point005_dominance : WallProjectionCheck 0 ownedP007 ownedP005 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP005]

theorem regime001_point006_dominance : WallProjectionCheck 0 ownedP007 ownedP006 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime001_point007_dominance : WallProjectionCheck 0 ownedP007 ownedP007 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime001_point009_dominance : WallProjectionCheck 0 ownedP009 ownedP009 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime001_point010_dominance : WallProjectionCheck 0 ownedP009 ownedP010 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP010]

theorem regime001_mirror15_005_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_005 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_005]

theorem regime001_mirror15_007_dominance : WallProjectionCheck 0 ownedP009 mirrorP15_007 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_007]

theorem regime001_mirror15_008_dominance : WallProjectionCheck 0 ownedP009 mirrorP15_008 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_008]

theorem regime001_mirror15_009_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_009 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_009]

theorem regime001_mirror15_010_dominance : WallProjectionCheck 0 ownedP007 mirrorP15_010 (1/16) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_010]

theorem regime001_checked : regime001.Check 0 0 points (1/16) (1/2) := by
  unfold regime001 AnchoredWallDirectionCertificate.Check
  refine ⟨facet009_mem, facet013_mem, facet012_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime001_point007
    · exact regime001_point009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime001_point005_dominance⟩
    · exact ⟨ownedP007, by simp, regime001_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime001_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point009_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point010_dominance⟩
    · exact ⟨ownedP007, by simp, regime001_mirror15_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror15_007_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror15_008_dominance⟩
    · exact ⟨ownedP007, by simp, regime001_mirror15_009_dominance⟩
    · exact ⟨ownedP007, by simp, regime001_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
