import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime015 : AnchoredWallDirectionCertificate := .ordinary facet001 facet011 [ownedP010, mirrorP08_005]

theorem regime015_guard : facet001.determinant facet011 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (1/4) (1) ∧
    (wallDualSecondPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (1/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011]

theorem regime015_point010_margin0 : (wallDualMargin facet001 facet011 3 ownedP010).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, ownedP010]

theorem regime015_point010 : WallDualCheck facet001 facet011 3 ownedP010 (1/4) (1) := by
  rcases regime015_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime015_point010_margin0⟩

theorem regime015_mirror08_005_margin0 : (wallDualMargin facet001 facet011 3 mirrorP08_005).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, mirrorP08_005]

theorem regime015_mirror08_005 : WallDualCheck facet001 facet011 3 mirrorP08_005 (1/4) (1) := by
  rcases regime015_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime015_mirror08_005_margin0⟩

theorem regime015_point006_dominance : WallProjectionCheck 3 ownedP010 ownedP006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP006]

theorem regime015_point007_dominance : WallProjectionCheck 3 ownedP010 ownedP007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP007]

theorem regime015_point008_dominance : WallProjectionCheck 3 ownedP010 ownedP008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP008]

theorem regime015_point009_dominance : WallProjectionCheck 3 ownedP010 ownedP009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP009]

theorem regime015_point010_dominance : WallProjectionCheck 3 ownedP010 ownedP010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime015_point011_dominance : WallProjectionCheck 3 ownedP010 ownedP011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP011]

theorem regime015_point012_dominance : WallProjectionCheck 3 ownedP010 ownedP012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP012]

theorem regime015_point013_dominance : WallProjectionCheck 3 ownedP010 ownedP013 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP013]

theorem regime015_point014_dominance : WallProjectionCheck 3 ownedP010 ownedP014 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP014]

theorem regime015_mirror08_005_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_005]

theorem regime015_mirror08_006_dominance : WallProjectionCheck 3 ownedP010 mirrorP08_006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP08_006]

theorem regime015_mirror08_007_dominance : WallProjectionCheck 3 ownedP010 mirrorP08_007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP08_007]

theorem regime015_mirror08_008_dominance : WallProjectionCheck 3 ownedP010 mirrorP08_008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP08_008]

theorem regime015_mirror08_010_dominance : WallProjectionCheck 3 ownedP010 mirrorP08_010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP08_010]

theorem regime015_mirror08_011_dominance : WallProjectionCheck 3 ownedP010 mirrorP08_011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP08_011]

theorem regime015_mirror08_012_dominance : WallProjectionCheck 3 ownedP010 mirrorP08_012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP08_012]

theorem regime015_mirror08_013_dominance : WallProjectionCheck 3 ownedP010 mirrorP08_013 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP08_013]

theorem regime015_checked : regime015.Check 7 3 points (1/4) (1) := by
  unfold regime015 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime015_point010
    · exact regime015_mirror08_005
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP010, by simp, regime015_point006_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point007_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point008_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point009_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point010_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point011_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point012_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point013_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_point014_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime015_mirror08_005_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_mirror08_006_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_mirror08_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_mirror08_008_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_mirror08_010_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_mirror08_011_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_mirror08_012_dominance⟩
    · exact ⟨ownedP010, by simp, regime015_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
