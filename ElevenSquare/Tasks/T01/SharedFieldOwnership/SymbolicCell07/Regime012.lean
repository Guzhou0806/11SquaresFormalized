import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime012 : AnchoredWallDirectionCertificate := .ordinary facet001 facet011 [ownedP008]

theorem regime012_guard : facet001.determinant facet011 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (0) (1/8) ∧
    (wallDualSecondPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (0) (1/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011]

theorem regime012_point008_margin0 : (wallDualMargin facet001 facet011 3 ownedP008).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, ownedP008]

theorem regime012_point008 : WallDualCheck facet001 facet011 3 ownedP008 (0) (1/8) := by
  rcases regime012_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime012_point008_margin0⟩

theorem regime012_point006_dominance : WallProjectionCheck 3 ownedP008 ownedP006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime012_point007_dominance : WallProjectionCheck 3 ownedP008 ownedP007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime012_point008_dominance : WallProjectionCheck 3 ownedP008 ownedP008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime012_point009_dominance : WallProjectionCheck 3 ownedP008 ownedP009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP009]

theorem regime012_point010_dominance : WallProjectionCheck 3 ownedP008 ownedP010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP010]

theorem regime012_point011_dominance : WallProjectionCheck 3 ownedP008 ownedP011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP011]

theorem regime012_point012_dominance : WallProjectionCheck 3 ownedP008 ownedP012 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP012]

theorem regime012_point013_dominance : WallProjectionCheck 3 ownedP008 ownedP013 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP013]

theorem regime012_point014_dominance : WallProjectionCheck 3 ownedP008 ownedP014 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP014]

theorem regime012_mirror08_005_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_005]

theorem regime012_mirror08_006_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_006]

theorem regime012_mirror08_007_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_007]

theorem regime012_mirror08_008_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_008]

theorem regime012_mirror08_010_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_010]

theorem regime012_mirror08_011_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_011]

theorem regime012_mirror08_012_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_012 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_012]

theorem regime012_mirror08_013_dominance : WallProjectionCheck 3 ownedP008 mirrorP08_013 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_013]

theorem regime012_checked : regime012.Check 7 3 points (0) (1/8) := by
  unfold regime012 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime012_point008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime012_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point008_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point009_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point010_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point011_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point012_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point013_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point014_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_007_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_010_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_011_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_012_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
