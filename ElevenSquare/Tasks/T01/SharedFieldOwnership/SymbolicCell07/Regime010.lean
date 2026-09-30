import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime010 : AnchoredWallDirectionCertificate := .ordinary facet014 facet019 [ownedP013]

theorem regime010_guard : facet014.determinant facet019 ≠ 0 ∧
    (wallDualFirstPolynomial facet014 facet019 2).quartic.BernsteinNonnegCheck (3/16) (1/4) ∧
    (wallDualSecondPolynomial facet014 facet019 2).quartic.BernsteinNonnegCheck (3/16) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet019]

theorem regime010_point013_margin0 : (wallDualMargin facet014 facet019 2 ownedP013).BernsteinPosCheck (3/16) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet014, facet019, ownedP013]

theorem regime010_point013 : WallDualCheck facet014 facet019 2 ownedP013 (3/16) (1/4) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point013_margin0⟩

theorem regime010_point006_dominance : WallProjectionCheck 2 ownedP013 ownedP006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP006]

theorem regime010_point007_dominance : WallProjectionCheck 2 ownedP013 ownedP007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP007]

theorem regime010_point008_dominance : WallProjectionCheck 2 ownedP013 ownedP008 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP008]

theorem regime010_point009_dominance : WallProjectionCheck 2 ownedP013 ownedP009 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP009]

theorem regime010_point010_dominance : WallProjectionCheck 2 ownedP013 ownedP010 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP010]

theorem regime010_point011_dominance : WallProjectionCheck 2 ownedP013 ownedP011 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP011]

theorem regime010_point012_dominance : WallProjectionCheck 2 ownedP013 ownedP012 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP012]

theorem regime010_point013_dominance : WallProjectionCheck 2 ownedP013 ownedP013 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP013]

theorem regime010_point014_dominance : WallProjectionCheck 2 ownedP013 ownedP014 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP014]

theorem regime010_mirror08_005_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_005 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_005]

theorem regime010_mirror08_006_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_006]

theorem regime010_mirror08_007_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_007]

theorem regime010_mirror08_008_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_008 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_008]

theorem regime010_mirror08_010_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_010 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_010]

theorem regime010_mirror08_011_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_011 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_011]

theorem regime010_mirror08_012_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_012 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_012]

theorem regime010_mirror08_013_dominance : WallProjectionCheck 2 ownedP013 mirrorP08_013 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_013]

theorem regime010_checked : regime010.Check 7 2 points (3/16) (1/4) := by
  unfold regime010 AnchoredWallDirectionCertificate.Check
  refine ⟨facet014_mem, facet019_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime010_point013
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP013, by simp, regime010_point006_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point007_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point008_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point009_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point010_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point011_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point012_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point013_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_point014_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_005_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_006_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_007_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_008_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_010_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_011_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_012_dominance⟩
    · exact ⟨ownedP013, by simp, regime010_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
