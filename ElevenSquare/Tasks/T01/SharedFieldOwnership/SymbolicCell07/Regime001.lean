import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime001 : AnchoredWallDirectionCertificate := .ordinary facet001 facet019 [ownedP011]

theorem regime001_guard : facet001.determinant facet019 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet019 0).quartic.BernsteinNonnegCheck (1/2) (5/8) ∧
    (wallDualSecondPolynomial facet001 facet019 0).quartic.BernsteinNonnegCheck (1/2) (5/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019]

theorem regime001_point011_margin0 : (wallDualMargin facet001 facet019 0 ownedP011).BernsteinPosCheck (1/2) (5/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet019, ownedP011]

theorem regime001_point011 : WallDualCheck facet001 facet019 0 ownedP011 (1/2) (5/8) := by
  rcases regime001_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime001_point011_margin0⟩

theorem regime001_point006_dominance : WallProjectionCheck 0 ownedP011 ownedP006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP006]

theorem regime001_point007_dominance : WallProjectionCheck 0 ownedP011 ownedP007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP007]

theorem regime001_point008_dominance : WallProjectionCheck 0 ownedP011 ownedP008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP008]

theorem regime001_point009_dominance : WallProjectionCheck 0 ownedP011 ownedP009 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP009]

theorem regime001_point010_dominance : WallProjectionCheck 0 ownedP011 ownedP010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP010]

theorem regime001_point011_dominance : WallProjectionCheck 0 ownedP011 ownedP011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime001_point012_dominance : WallProjectionCheck 0 ownedP011 ownedP012 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP012]

theorem regime001_point013_dominance : WallProjectionCheck 0 ownedP011 ownedP013 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP013]

theorem regime001_point014_dominance : WallProjectionCheck 0 ownedP011 ownedP014 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP014]

theorem regime001_mirror08_005_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_005 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_005]

theorem regime001_mirror08_006_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_006]

theorem regime001_mirror08_007_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_007]

theorem regime001_mirror08_008_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_008]

theorem regime001_mirror08_010_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_010]

theorem regime001_mirror08_011_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_011]

theorem regime001_mirror08_012_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_012 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_012]

theorem regime001_mirror08_013_dominance : WallProjectionCheck 0 ownedP011 mirrorP08_013 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP08_013]

theorem regime001_checked : regime001.Check 7 0 points (1/2) (5/8) := by
  unfold regime001 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet019_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime001_point011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP011, by simp, regime001_point006_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point007_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point008_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point009_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point011_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point012_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point013_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_point014_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_005_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_006_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_007_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_008_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_010_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_011_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_012_dominance⟩
    · exact ⟨ownedP011, by simp, regime001_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
