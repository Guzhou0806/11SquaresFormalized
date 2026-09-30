import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime000 : AnchoredWallDirectionCertificate := .ordinary facet001 facet019 [ownedP011]

theorem regime000_guard : facet001.determinant facet019 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet019 0).quartic.BernsteinNonnegCheck (0) (1/2) ∧
    (wallDualSecondPolynomial facet001 facet019 0).quartic.BernsteinNonnegCheck (0) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019]

theorem regime000_point011_margin0 : (wallDualMargin facet001 facet019 0 ownedP011).BernsteinPosCheck (0) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, ownedP011]

theorem regime000_point011 : WallDualCheck facet001 facet019 0 ownedP011 (0) (1/2) := by
  rcases regime000_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime000_point011_margin0⟩

theorem regime000_point006_dominance : WallProjectionCheck 0 ownedP011 ownedP006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP006]

theorem regime000_point007_dominance : WallProjectionCheck 0 ownedP011 ownedP007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP007]

theorem regime000_point008_dominance : WallProjectionCheck 0 ownedP011 ownedP008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP008]

theorem regime000_point009_dominance : WallProjectionCheck 0 ownedP011 ownedP009 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP009]

theorem regime000_point010_dominance : WallProjectionCheck 0 ownedP011 ownedP010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP010]

theorem regime000_point011_dominance : WallProjectionCheck 0 ownedP011 ownedP011 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime000_point012_dominance : WallProjectionCheck 0 ownedP011 ownedP012 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP012]

theorem regime000_point013_dominance : WallProjectionCheck 0 ownedP011 ownedP013 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP013]

theorem regime000_point014_dominance : WallProjectionCheck 0 ownedP011 ownedP014 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP014]

theorem regime000_mirror08_005_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_005 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_005]

theorem regime000_mirror08_006_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_006 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_006]

theorem regime000_mirror08_007_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_007 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_007]

theorem regime000_mirror08_008_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_008 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_008]

theorem regime000_mirror08_010_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_010 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_010]

theorem regime000_mirror08_011_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_011 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_011]

theorem regime000_mirror08_012_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_012 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_012]

theorem regime000_mirror08_013_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_013 (0) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_013]

theorem regime000_checked : regime000.Check 7 0 points (0) (1/2) := by
  unfold regime000 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet019_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime000_point011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP011, by simp, regime000_point006_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point007_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point008_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point009_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point011_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point012_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point013_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_point014_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_005_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_006_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_007_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_008_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_010_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_011_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_012_dominance⟩
    · exact ⟨ownedP011, by simp, regime000_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
