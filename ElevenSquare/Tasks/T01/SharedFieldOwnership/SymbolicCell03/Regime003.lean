import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime003 : AnchoredWallDirectionCertificate := .ordinary facet002 facet010 [mirrorP12_009]

theorem regime003_guard : facet002.determinant facet010 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet010 1).quartic.BernsteinNonnegCheck (0) (1/8) ∧
    (wallDualSecondPolynomial facet002 facet010 1).quartic.BernsteinNonnegCheck (0) (1/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010]

theorem regime003_mirror12_009_margin0 : (wallDualMargin facet002 facet010 1 mirrorP12_009).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, mirrorP12_009]

theorem regime003_mirror12_009 : WallDualCheck facet002 facet010 1 mirrorP12_009 (0) (1/8) := by
  rcases regime003_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime003_mirror12_009_margin0⟩

theorem regime003_point005_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP005]

theorem regime003_point006_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP006]

theorem regime003_point007_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP007]

theorem regime003_point008_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP008]

theorem regime003_point009_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP009]

theorem regime003_point010_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP010]

theorem regime003_point011_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP011]

theorem regime003_mirror12_005_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_005]

theorem regime003_mirror12_006_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_006]

theorem regime003_mirror12_007_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_007]

theorem regime003_mirror12_008_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_008]

theorem regime003_mirror12_009_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_009]

theorem regime003_mirror12_010_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_010]

theorem regime003_mirror12_011_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_011]

theorem regime003_checked : regime003.Check 3 1 points (0) (1/8) := by
  unfold regime003 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime003_mirror12_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP12_009, by simp, regime003_point005_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_point006_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_point007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_point008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_point009_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_point010_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_point011_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_mirror12_005_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_mirror12_006_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_mirror12_007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_mirror12_008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_mirror12_009_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_mirror12_010_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime003_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
