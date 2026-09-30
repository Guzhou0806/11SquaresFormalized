import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime011 : AnchoredWallDirectionCertificate := .crossing facet002 facet009 facet013 (536422000000/286195087637) [ownedP007]

theorem regime011_guard : facet002.determinant facet009 ≠ 0 ∧
    facet009.determinant facet013 ≠ 0 ∧
    0 < (536422000000/286195087637:ℚ) ∧
    wallDualSecondPolynomial facet009 facet013 3 = (wallDualFirstPolynomial facet002 facet009 3).negScale (536422000000/286195087637) ∧
    (wallDualSecondPolynomial facet002 facet009 3).quartic.BernsteinNonnegCheck (2973/4096) (1) ∧
    (wallDualFirstPolynomial facet009 facet013 3).quartic.BernsteinNonnegCheck (2973/4096) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009, facet013]

theorem regime011_point007_margin0 : (wallDualMargin facet002 facet009 3 ownedP007).BernsteinPosCheck (2973/4096) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009, facet013, ownedP007]

theorem regime011_point007_margin1 : (wallDualMargin facet009 facet013 3 ownedP007).BernsteinPosCheck (2973/4096) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet009, facet013, ownedP007]

theorem regime011_point007 : WallDualCrossingCheck facet002 facet009 facet013 3 ownedP007 (2973/4096) (1) (536422000000/286195087637) := by
  rcases regime011_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime011_point007_margin0, regime011_point007_margin1⟩

theorem regime011_point005_dominance : WallProjectionCheck 3 ownedP007 ownedP005 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP005]

theorem regime011_point006_dominance : WallProjectionCheck 3 ownedP007 ownedP006 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime011_point007_dominance : WallProjectionCheck 3 ownedP007 ownedP007 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime011_point009_dominance : WallProjectionCheck 3 ownedP007 ownedP009 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime011_point010_dominance : WallProjectionCheck 3 ownedP007 ownedP010 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP010]

theorem regime011_mirror15_005_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_005 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_005]

theorem regime011_mirror15_007_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_007 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_007]

theorem regime011_mirror15_008_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_008 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_008]

theorem regime011_mirror15_009_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_009 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_009]

theorem regime011_mirror15_010_dominance : WallProjectionCheck 3 ownedP007 mirrorP15_010 (2973/4096) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP15_010]

theorem regime011_checked : regime011.Check 0 3 points (2973/4096) (1) := by
  unfold regime011 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet009_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime011_point007
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime011_point005_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_point007_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_point010_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror15_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror15_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror15_008_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror15_009_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
