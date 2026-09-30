import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime011 : AnchoredWallDirectionCertificate := .crossing facet002 facet011 facet014 (57985000000/32183995753) [ownedP007]

theorem regime011_guard : facet002.determinant facet011 ≠ 0 ∧
    facet011.determinant facet014 ≠ 0 ∧
    0 < (57985000000/32183995753:ℚ) ∧
    wallDualSecondPolynomial facet011 facet014 3 = (wallDualFirstPolynomial facet002 facet011 3).negScale (57985000000/32183995753) ∧
    (wallDualSecondPolynomial facet002 facet011 3).quartic.BernsteinNonnegCheck (3/4) (1) ∧
    (wallDualFirstPolynomial facet011 facet014 3).quartic.BernsteinNonnegCheck (3/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011, facet014]

theorem regime011_point007_margin0 : (wallDualMargin facet002 facet011 3 ownedP007).BernsteinPosCheck (3/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011, facet014, ownedP007]

theorem regime011_point007_margin1 : (wallDualMargin facet011 facet014 3 ownedP007).BernsteinPosCheck (3/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet011, facet014, ownedP007]

theorem regime011_point007 : WallDualCrossingCheck facet002 facet011 facet014 3 ownedP007 (3/4) (1) (57985000000/32183995753) := by
  rcases regime011_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime011_point007_margin0, regime011_point007_margin1⟩

theorem regime011_point005_dominance : WallProjectionCheck 3 ownedP007 ownedP005 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP005]

theorem regime011_point006_dominance : WallProjectionCheck 3 ownedP007 ownedP006 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime011_point007_dominance : WallProjectionCheck 3 ownedP007 ownedP007 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime011_point008_dominance : WallProjectionCheck 3 ownedP007 ownedP008 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP008]

theorem regime011_point009_dominance : WallProjectionCheck 3 ownedP007 ownedP009 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime011_mirror13_005_dominance : WallProjectionCheck 3 ownedP007 mirrorP13_005 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_005]

theorem regime011_mirror13_006_dominance : WallProjectionCheck 3 ownedP007 mirrorP13_006 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_006]

theorem regime011_mirror13_007_dominance : WallProjectionCheck 3 ownedP007 mirrorP13_007 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_007]

theorem regime011_mirror13_010_dominance : WallProjectionCheck 3 ownedP007 mirrorP13_010 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_010]

theorem regime011_mirror13_011_dominance : WallProjectionCheck 3 ownedP007 mirrorP13_011 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP13_011]

theorem regime011_checked : regime011.Check 2 3 points (3/4) (1) := by
  unfold regime011 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet011_mem, facet014_mem, ?_, ?_⟩
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
    · exact ⟨ownedP007, by simp, regime011_point008_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror13_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror13_006_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror13_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror13_010_dominance⟩
    · exact ⟨ownedP007, by simp, regime011_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
