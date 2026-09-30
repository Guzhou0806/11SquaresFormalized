import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime004 : AnchoredWallDirectionCertificate := .ordinary facet002 facet010 [mirrorP12_009, mirrorP12_010, mirrorP12_011]

theorem regime004_guard : facet002.determinant facet010 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet010 1).quartic.BernsteinNonnegCheck (1/8) (1/4) ∧
    (wallDualSecondPolynomial facet002 facet010 1).quartic.BernsteinNonnegCheck (1/8) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010]

theorem regime004_mirror12_009_margin0 : (wallDualMargin facet002 facet010 1 mirrorP12_009).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, mirrorP12_009]

theorem regime004_mirror12_009 : WallDualCheck facet002 facet010 1 mirrorP12_009 (1/8) (1/4) := by
  rcases regime004_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime004_mirror12_009_margin0⟩

theorem regime004_mirror12_010_margin0 : (wallDualMargin facet002 facet010 1 mirrorP12_010).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, mirrorP12_010]

theorem regime004_mirror12_010 : WallDualCheck facet002 facet010 1 mirrorP12_010 (1/8) (1/4) := by
  rcases regime004_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime004_mirror12_010_margin0⟩

theorem regime004_mirror12_011_margin0 : (wallDualMargin facet002 facet010 1 mirrorP12_011).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, mirrorP12_011]

theorem regime004_mirror12_011 : WallDualCheck facet002 facet010 1 mirrorP12_011 (1/8) (1/4) := by
  rcases regime004_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime004_mirror12_011_margin0⟩

theorem regime004_point005_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP005 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP005]

theorem regime004_point006_dominance : WallProjectionCheck 1 mirrorP12_010 ownedP006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_010, ownedP006]

theorem regime004_point007_dominance : WallProjectionCheck 1 mirrorP12_011 ownedP007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, ownedP007]

theorem regime004_point008_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP008]

theorem regime004_point009_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP009 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP009]

theorem regime004_point010_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP010]

theorem regime004_point011_dominance : WallProjectionCheck 1 mirrorP12_009 ownedP011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, ownedP011]

theorem regime004_mirror12_005_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_005 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_005]

theorem regime004_mirror12_006_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_006]

theorem regime004_mirror12_007_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_007]

theorem regime004_mirror12_008_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_008]

theorem regime004_mirror12_009_dominance : WallProjectionCheck 1 mirrorP12_009 mirrorP12_009 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_009, mirrorP12_009]

theorem regime004_mirror12_010_dominance : WallProjectionCheck 1 mirrorP12_010 mirrorP12_010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_010, mirrorP12_010]

theorem regime004_mirror12_011_dominance : WallProjectionCheck 1 mirrorP12_011 mirrorP12_011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP12_011, mirrorP12_011]

theorem regime004_checked : regime004.Check 3 1 points (1/8) (1/4) := by
  unfold regime004 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact regime004_mirror12_009
    · exact regime004_mirror12_010
    · exact regime004_mirror12_011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP12_009, by simp, regime004_point005_dominance⟩
    · exact ⟨mirrorP12_010, by simp, regime004_point006_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime004_point007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_point008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_point009_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_point010_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_point011_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_mirror12_005_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_mirror12_006_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_mirror12_007_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_mirror12_008_dominance⟩
    · exact ⟨mirrorP12_009, by simp, regime004_mirror12_009_dominance⟩
    · exact ⟨mirrorP12_010, by simp, regime004_mirror12_010_dominance⟩
    · exact ⟨mirrorP12_011, by simp, regime004_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
