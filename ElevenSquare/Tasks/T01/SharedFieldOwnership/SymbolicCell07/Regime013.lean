import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime013 : AnchoredWallDirectionCertificate := .ordinary facet001 facet011 [ownedP008, ownedP014, mirrorP08_013]

theorem regime013_guard : facet001.determinant facet011 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (1/8) (3/16) ∧
    (wallDualSecondPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (1/8) (3/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011]

theorem regime013_point008_margin0 : (wallDualMargin facet001 facet011 3 ownedP008).BernsteinPosCheck (1/8) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, ownedP008]

theorem regime013_point008 : WallDualCheck facet001 facet011 3 ownedP008 (1/8) (3/16) := by
  rcases regime013_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime013_point008_margin0⟩

theorem regime013_point014_margin0 : (wallDualMargin facet001 facet011 3 ownedP014).BernsteinPosCheck (1/8) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, ownedP014]

theorem regime013_point014 : WallDualCheck facet001 facet011 3 ownedP014 (1/8) (3/16) := by
  rcases regime013_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime013_point014_margin0⟩

theorem regime013_mirror08_013_margin0 : (wallDualMargin facet001 facet011 3 mirrorP08_013).BernsteinPosCheck (1/8) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, mirrorP08_013]

theorem regime013_mirror08_013 : WallDualCheck facet001 facet011 3 mirrorP08_013 (1/8) (3/16) := by
  rcases regime013_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime013_mirror08_013_margin0⟩

theorem regime013_point006_dominance : WallProjectionCheck 3 ownedP008 ownedP006 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime013_point007_dominance : WallProjectionCheck 3 ownedP008 ownedP007 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime013_point008_dominance : WallProjectionCheck 3 ownedP008 ownedP008 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime013_point009_dominance : WallProjectionCheck 3 mirrorP08_013 ownedP009 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_013, ownedP009]

theorem regime013_point010_dominance : WallProjectionCheck 3 ownedP014 ownedP010 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP014, ownedP010]

theorem regime013_point011_dominance : WallProjectionCheck 3 ownedP008 ownedP011 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP011]

theorem regime013_point012_dominance : WallProjectionCheck 3 ownedP008 ownedP012 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP012]

theorem regime013_point013_dominance : WallProjectionCheck 3 ownedP008 ownedP013 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP013]

theorem regime013_point014_dominance : WallProjectionCheck 3 ownedP014 ownedP014 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP014, ownedP014]

theorem regime013_mirror08_005_dominance : WallProjectionCheck 3 ownedP014 mirrorP08_005 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP014, mirrorP08_005]

theorem regime013_mirror08_006_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_006 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_006]

theorem regime013_mirror08_007_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_007 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_007]

theorem regime013_mirror08_008_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_008 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_008]

theorem regime013_mirror08_010_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_010 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_010]

theorem regime013_mirror08_011_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_011 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_011]

theorem regime013_mirror08_012_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_012 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_012]

theorem regime013_mirror08_013_dominance : WallProjectionCheck 3 mirrorP08_013 mirrorP08_013 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_013, mirrorP08_013]

theorem regime013_checked : regime013.Check 7 3 points (1/8) (3/16) := by
  unfold regime013 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact regime013_point008
    · exact regime013_point014
    · exact regime013_mirror08_013
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime013_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_point008_dominance⟩
    · exact ⟨mirrorP08_013, by simp, regime013_point009_dominance⟩
    · exact ⟨ownedP014, by simp, regime013_point010_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_point011_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_point012_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_point013_dominance⟩
    · exact ⟨ownedP014, by simp, regime013_point014_dominance⟩
    · exact ⟨ownedP014, by simp, regime013_mirror08_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_mirror08_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_mirror08_007_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_mirror08_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_mirror08_010_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_mirror08_011_dominance⟩
    · exact ⟨ownedP008, by simp, regime013_mirror08_012_dominance⟩
    · exact ⟨mirrorP08_013, by simp, regime013_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
