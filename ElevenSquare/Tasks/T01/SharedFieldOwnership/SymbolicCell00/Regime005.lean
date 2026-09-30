import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime005 : AnchoredWallDirectionCertificate := .crossing facet001 facet012 facet000 (1) [ownedP009]

theorem regime005_guard : facet001.determinant facet012 ≠ 0 ∧
    facet012.determinant facet000 ≠ 0 ∧
    0 < (1:ℚ) ∧
    wallDualSecondPolynomial facet012 facet000 2 = (wallDualFirstPolynomial facet001 facet012 2).negScale (1) ∧
    (wallDualSecondPolynomial facet001 facet012 2).quartic.BernsteinNonnegCheck (0) (1/8) ∧
    (wallDualFirstPolynomial facet012 facet000 2).quartic.BernsteinNonnegCheck (0) (1/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet012, facet000]

theorem regime005_point009_margin0 : (wallDualMargin facet001 facet012 2 ownedP009).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet012, facet000, ownedP009]

theorem regime005_point009_margin1 : (wallDualMargin facet012 facet000 2 ownedP009).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet012, facet000, ownedP009]

theorem regime005_point009 : WallDualCrossingCheck facet001 facet012 facet000 2 ownedP009 (0) (1/8) (1) := by
  rcases regime005_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime005_point009_margin0, regime005_point009_margin1⟩

theorem regime005_point005_dominance : WallProjectionCheck 2 ownedP009 ownedP005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP005]

theorem regime005_point006_dominance : WallProjectionCheck 2 ownedP009 ownedP006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP006]

theorem regime005_point007_dominance : WallProjectionCheck 2 ownedP009 ownedP007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime005_point009_dominance : WallProjectionCheck 2 ownedP009 ownedP009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime005_point010_dominance : WallProjectionCheck 2 ownedP009 ownedP010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP010]

theorem regime005_mirror15_005_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_005]

theorem regime005_mirror15_007_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_007]

theorem regime005_mirror15_008_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_008]

theorem regime005_mirror15_009_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_009]

theorem regime005_mirror15_010_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_010]

theorem regime005_checked : regime005.Check 0 2 points (0) (1/8) := by
  unfold regime005 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet012_mem, facet000_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime005_point009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP009, by simp, regime005_point005_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_point006_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_point009_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_point010_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_mirror15_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_mirror15_007_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_mirror15_008_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_mirror15_009_dominance⟩
    · exact ⟨ownedP009, by simp, regime005_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
