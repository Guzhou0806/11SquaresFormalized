import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime004 : AnchoredWallDirectionCertificate := .ordinary facet009 facet013 [mirrorP13_010]

theorem regime004_guard : facet009.determinant facet013 ≠ 0 ∧
    (wallDualFirstPolynomial facet009 facet013 1).quartic.BernsteinNonnegCheck (0) (711/4096) ∧
    (wallDualSecondPolynomial facet009 facet013 1).quartic.BernsteinNonnegCheck (0) (711/4096) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013]

theorem regime004_mirror13_010_margin0 : (wallDualMargin facet009 facet013 1 mirrorP13_010).BernsteinPosCheck (0) (711/4096) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet009, facet013, mirrorP13_010]

theorem regime004_mirror13_010 : WallDualCheck facet009 facet013 1 mirrorP13_010 (0) (711/4096) := by
  rcases regime004_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime004_mirror13_010_margin0⟩

theorem regime004_point005_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP005 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP005]

theorem regime004_point006_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP006 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP006]

theorem regime004_point007_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP007 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP007]

theorem regime004_point008_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP008 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP008]

theorem regime004_point009_dominance : WallProjectionCheck 1 mirrorP13_010 ownedP009 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, ownedP009]

theorem regime004_mirror13_005_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_005 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_005]

theorem regime004_mirror13_006_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_006 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_006]

theorem regime004_mirror13_007_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_007 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_007]

theorem regime004_mirror13_010_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_010 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_010]

theorem regime004_mirror13_011_dominance : WallProjectionCheck 1 mirrorP13_010 mirrorP13_011 (0) (711/4096) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP13_010, mirrorP13_011]

theorem regime004_checked : regime004.Check 2 1 points (0) (711/4096) := by
  unfold regime004 AnchoredWallDirectionCertificate.Check
  refine ⟨facet009_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime004_mirror13_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP13_010, by simp, regime004_point005_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_point006_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_point007_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_point008_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_point009_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_mirror13_005_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_mirror13_006_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_mirror13_007_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_mirror13_010_dominance⟩
    · exact ⟨mirrorP13_010, by simp, regime004_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
