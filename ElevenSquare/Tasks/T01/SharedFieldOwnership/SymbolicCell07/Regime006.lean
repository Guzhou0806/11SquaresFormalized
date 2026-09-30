import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime006 : AnchoredWallDirectionCertificate := .crossing facet014 facet010 facet011 (40575309727/31364411136) [ownedP007]

theorem regime006_guard : facet014.determinant facet010 ≠ 0 ∧
    facet010.determinant facet011 ≠ 0 ∧
    0 < (40575309727/31364411136:ℚ) ∧
    wallDualSecondPolynomial facet010 facet011 1 = (wallDualFirstPolynomial facet014 facet010 1).negScale (40575309727/31364411136) ∧
    (wallDualSecondPolynomial facet014 facet010 1).quartic.BernsteinNonnegCheck (1/4) (7/16) ∧
    (wallDualFirstPolynomial facet010 facet011 1).quartic.BernsteinNonnegCheck (1/4) (7/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet010, facet011]

theorem regime006_point007_margin0 : (wallDualMargin facet014 facet010 1 ownedP007).BernsteinPosCheck (1/4) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet010, facet011, ownedP007]

theorem regime006_point007_margin1 : (wallDualMargin facet010 facet011 1 ownedP007).BernsteinPosCheck (1/4) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet010, facet011, ownedP007]

theorem regime006_point007 : WallDualCrossingCheck facet014 facet010 facet011 1 ownedP007 (1/4) (7/16) (40575309727/31364411136) := by
  rcases regime006_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime006_point007_margin0, regime006_point007_margin1⟩

theorem regime006_point006_dominance : WallProjectionCheck 1 ownedP007 ownedP006 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP006]

theorem regime006_point007_dominance : WallProjectionCheck 1 ownedP007 ownedP007 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP007]

theorem regime006_point008_dominance : WallProjectionCheck 1 ownedP007 ownedP008 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP008]

theorem regime006_point009_dominance : WallProjectionCheck 1 ownedP007 ownedP009 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP009]

theorem regime006_point010_dominance : WallProjectionCheck 1 ownedP007 ownedP010 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP010]

theorem regime006_point011_dominance : WallProjectionCheck 1 ownedP007 ownedP011 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP011]

theorem regime006_point012_dominance : WallProjectionCheck 1 ownedP007 ownedP012 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP012]

theorem regime006_point013_dominance : WallProjectionCheck 1 ownedP007 ownedP013 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP013]

theorem regime006_point014_dominance : WallProjectionCheck 1 ownedP007 ownedP014 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, ownedP014]

theorem regime006_mirror08_005_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_005 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_005]

theorem regime006_mirror08_006_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_006 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_006]

theorem regime006_mirror08_007_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_007 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_007]

theorem regime006_mirror08_008_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_008 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_008]

theorem regime006_mirror08_010_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_010 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_010]

theorem regime006_mirror08_011_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_011 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_011]

theorem regime006_mirror08_012_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_012 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_012]

theorem regime006_mirror08_013_dominance : WallProjectionCheck 1 ownedP007 mirrorP08_013 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP007, mirrorP08_013]

theorem regime006_checked : regime006.Check 7 1 points (1/4) (7/16) := by
  unfold regime006 AnchoredWallDirectionCertificate.Check
  refine ⟨facet014_mem, facet010_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime006_point007
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP007, by simp, regime006_point006_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point007_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point008_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point009_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point010_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point011_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point012_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point013_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_point014_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_005_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_006_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_007_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_008_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_010_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_011_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_012_dominance⟩
    · exact ⟨ownedP007, by simp, regime006_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
