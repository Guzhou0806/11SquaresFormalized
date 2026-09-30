import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime012 : AnchoredWallDirectionCertificate := .ordinary facet001 facet002 [ownedP008, mirrorP12_005]

theorem regime012_guard : facet001.determinant facet002 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet002 3).quartic.BernsteinNonnegCheck (0) (1) ∧
    (wallDualSecondPolynomial facet001 facet002 3).quartic.BernsteinNonnegCheck (0) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet002]

theorem regime012_point008_margin0 : (wallDualMargin facet001 facet002 3 ownedP008).BernsteinPosCheck (0) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet002, ownedP008]

theorem regime012_point008 : WallDualCheck facet001 facet002 3 ownedP008 (0) (1) := by
  rcases regime012_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime012_point008_margin0⟩

theorem regime012_mirror12_005_margin0 : (wallDualMargin facet001 facet002 3 mirrorP12_005).BernsteinPosCheck (0) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet002, mirrorP12_005]

theorem regime012_mirror12_005 : WallDualCheck facet001 facet002 3 mirrorP12_005 (0) (1) := by
  rcases regime012_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime012_mirror12_005_margin0⟩

theorem regime012_point005_dominance : WallProjectionCheck 3 ownedP008 ownedP005 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP005]

theorem regime012_point006_dominance : WallProjectionCheck 3 ownedP008 ownedP006 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime012_point007_dominance : WallProjectionCheck 3 ownedP008 ownedP007 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime012_point008_dominance : WallProjectionCheck 3 ownedP008 ownedP008 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime012_point009_dominance : WallProjectionCheck 3 ownedP008 ownedP009 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP009]

theorem regime012_point010_dominance : WallProjectionCheck 3 ownedP008 ownedP010 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP010]

theorem regime012_point011_dominance : WallProjectionCheck 3 ownedP008 ownedP011 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP011]

theorem regime012_mirror12_005_dominance : WallProjectionCheck 3 mirrorP12_005 mirrorP12_005 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_005, mirrorP12_005]

theorem regime012_mirror12_006_dominance : WallProjectionCheck 3 ownedP008 mirrorP12_006 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP12_006]

theorem regime012_mirror12_007_dominance : WallProjectionCheck 3 ownedP008 mirrorP12_007 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP12_007]

theorem regime012_mirror12_008_dominance : WallProjectionCheck 3 ownedP008 mirrorP12_008 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP12_008]

theorem regime012_mirror12_009_dominance : WallProjectionCheck 3 ownedP008 mirrorP12_009 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP12_009]

theorem regime012_mirror12_010_dominance : WallProjectionCheck 3 ownedP008 mirrorP12_010 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP12_010]

theorem regime012_mirror12_011_dominance : WallProjectionCheck 3 mirrorP12_005 mirrorP12_011 (0) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_005, mirrorP12_011]

theorem regime012_checked : regime012.Check 3 3 points (0) (1) := by
  unfold regime012 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet002_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime012_point008
    · exact regime012_mirror12_005
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime012_point005_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point008_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point009_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point010_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_point011_dominance⟩
    · exact ⟨mirrorP12_005, by simp, regime012_mirror12_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror12_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror12_007_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror12_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror12_009_dominance⟩
    · exact ⟨ownedP008, by simp, regime012_mirror12_010_dominance⟩
    · exact ⟨mirrorP12_005, by simp, regime012_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
