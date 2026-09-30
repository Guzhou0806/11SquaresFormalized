import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime014 : AnchoredWallDirectionCertificate := .ordinary facet001 facet011 [mirrorP08_005, mirrorP08_013]

theorem regime014_guard : facet001.determinant facet011 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (3/16) (1/4) ∧
    (wallDualSecondPolynomial facet001 facet011 3).quartic.BernsteinNonnegCheck (3/16) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011]

theorem regime014_mirror08_005_margin0 : (wallDualMargin facet001 facet011 3 mirrorP08_005).BernsteinPosCheck (3/16) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, mirrorP08_005]

theorem regime014_mirror08_005 : WallDualCheck facet001 facet011 3 mirrorP08_005 (3/16) (1/4) := by
  rcases regime014_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime014_mirror08_005_margin0⟩

theorem regime014_mirror08_013_margin0 : (wallDualMargin facet001 facet011 3 mirrorP08_013).BernsteinPosCheck (3/16) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet011, mirrorP08_013]

theorem regime014_mirror08_013 : WallDualCheck facet001 facet011 3 mirrorP08_013 (3/16) (1/4) := by
  rcases regime014_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime014_mirror08_013_margin0⟩

theorem regime014_point006_dominance : WallProjectionCheck 3 mirrorP08_005 ownedP006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, ownedP006]

theorem regime014_point007_dominance : WallProjectionCheck 3 mirrorP08_005 ownedP007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, ownedP007]

theorem regime014_point008_dominance : WallProjectionCheck 3 mirrorP08_005 ownedP008 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, ownedP008]

theorem regime014_point009_dominance : WallProjectionCheck 3 mirrorP08_013 ownedP009 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_013, ownedP009]

theorem regime014_point010_dominance : WallProjectionCheck 3 mirrorP08_005 ownedP010 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, ownedP010]

theorem regime014_point011_dominance : WallProjectionCheck 3 mirrorP08_005 ownedP011 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, ownedP011]

theorem regime014_point012_dominance : WallProjectionCheck 3 mirrorP08_005 ownedP012 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, ownedP012]

theorem regime014_point013_dominance : WallProjectionCheck 3 mirrorP08_005 ownedP013 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, ownedP013]

theorem regime014_point014_dominance : WallProjectionCheck 3 mirrorP08_013 ownedP014 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_013, ownedP014]

theorem regime014_mirror08_005_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_005 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_005]

theorem regime014_mirror08_006_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_006]

theorem regime014_mirror08_007_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_007]

theorem regime014_mirror08_008_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_008 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_008]

theorem regime014_mirror08_010_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_010 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_010]

theorem regime014_mirror08_011_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_011 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_011]

theorem regime014_mirror08_012_dominance : WallProjectionCheck 3 mirrorP08_005 mirrorP08_012 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_005, mirrorP08_012]

theorem regime014_mirror08_013_dominance : WallProjectionCheck 3 mirrorP08_013 mirrorP08_013 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP08_013, mirrorP08_013]

theorem regime014_checked : regime014.Check 7 3 points (3/16) (1/4) := by
  unfold regime014 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet011_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime014_mirror08_005
    · exact regime014_mirror08_013
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP08_005, by simp, regime014_point006_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_point007_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_point008_dominance⟩
    · exact ⟨mirrorP08_013, by simp, regime014_point009_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_point010_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_point011_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_point012_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_point013_dominance⟩
    · exact ⟨mirrorP08_013, by simp, regime014_point014_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_mirror08_005_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_mirror08_006_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_mirror08_007_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_mirror08_008_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_mirror08_010_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_mirror08_011_dominance⟩
    · exact ⟨mirrorP08_005, by simp, regime014_mirror08_012_dominance⟩
    · exact ⟨mirrorP08_013, by simp, regime014_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
