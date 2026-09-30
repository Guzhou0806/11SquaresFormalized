import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime002 : AnchoredWallDirectionCertificate := .ordinary facet001 facet019 [ownedP011, ownedP012, ownedP013]

theorem regime002_guard : facet001.determinant facet019 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet019 0).quartic.BernsteinNonnegCheck (5/8) (3/4) ∧
    (wallDualSecondPolynomial facet001 facet019 0).quartic.BernsteinNonnegCheck (5/8) (3/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019]

theorem regime002_point011_margin0 : (wallDualMargin facet001 facet019 0 ownedP011).BernsteinPosCheck (5/8) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, ownedP011]

theorem regime002_point011 : WallDualCheck facet001 facet019 0 ownedP011 (5/8) (3/4) := by
  rcases regime002_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime002_point011_margin0⟩

theorem regime002_point012_margin0 : (wallDualMargin facet001 facet019 0 ownedP012).BernsteinPosCheck (5/8) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, ownedP012]

theorem regime002_point012 : WallDualCheck facet001 facet019 0 ownedP012 (5/8) (3/4) := by
  rcases regime002_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime002_point012_margin0⟩

theorem regime002_point013_margin0 : (wallDualMargin facet001 facet019 0 ownedP013).BernsteinPosCheck (5/8) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, ownedP013]

theorem regime002_point013 : WallDualCheck facet001 facet019 0 ownedP013 (5/8) (3/4) := by
  rcases regime002_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime002_point013_margin0⟩

theorem regime002_point006_dominance : WallProjectionCheck 0 ownedP011 ownedP006 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP006]

theorem regime002_point007_dominance : WallProjectionCheck 0 ownedP011 ownedP007 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP007]

theorem regime002_point008_dominance : WallProjectionCheck 0 ownedP011 ownedP008 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP008]

theorem regime002_point009_dominance : WallProjectionCheck 0 ownedP011 ownedP009 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP009]

theorem regime002_point010_dominance : WallProjectionCheck 0 ownedP011 ownedP010 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP010]

theorem regime002_point011_dominance : WallProjectionCheck 0 ownedP011 ownedP011 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime002_point012_dominance : WallProjectionCheck 0 ownedP012 ownedP012 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP012, ownedP012]

theorem regime002_point013_dominance : WallProjectionCheck 0 ownedP013 ownedP013 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, ownedP013]

theorem regime002_point014_dominance : WallProjectionCheck 0 ownedP011 ownedP014 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP014]

theorem regime002_mirror08_005_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_005 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_005]

theorem regime002_mirror08_006_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_006 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_006]

theorem regime002_mirror08_007_dominance : WallProjectionCheck 0 ownedP012 mirrorP08_007 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP012, mirrorP08_007]

theorem regime002_mirror08_008_dominance : WallProjectionCheck 0 ownedP013 mirrorP08_008 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP013, mirrorP08_008]

theorem regime002_mirror08_010_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_010 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_010]

theorem regime002_mirror08_011_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_011 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_011]

theorem regime002_mirror08_012_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_012 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_012]

theorem regime002_mirror08_013_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_013 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_013]

theorem regime002_checked : regime002.Check 7 0 points (5/8) (3/4) := by
  unfold regime002 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet019_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact regime002_point011
    · exact regime002_point012
    · exact regime002_point013
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP011, by simp, regime002_point006_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_point007_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_point008_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_point009_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_point011_dominance⟩
    · exact ⟨ownedP012, by simp, regime002_point012_dominance⟩
    · exact ⟨ownedP013, by simp, regime002_point013_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_point014_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_mirror08_005_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_mirror08_006_dominance⟩
    · exact ⟨ownedP012, by simp, regime002_mirror08_007_dominance⟩
    · exact ⟨ownedP013, by simp, regime002_mirror08_008_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_mirror08_010_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_mirror08_011_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_mirror08_012_dominance⟩
    · exact ⟨ownedP011, by simp, regime002_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
