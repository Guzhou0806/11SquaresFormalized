import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime007 : AnchoredWallDirectionCertificate := .ordinary facet000 facet008 [ownedP008, mirrorP11_010, mirrorP11_011]

theorem regime007_guard : facet000.determinant facet008 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (5/8) (3/4) ∧
    (wallDualSecondPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (5/8) (3/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008]

theorem regime007_point008_margin0 : (wallDualMargin facet000 facet008 1 ownedP008).BernsteinPosCheck (5/8) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, ownedP008]

theorem regime007_point008 : WallDualCheck facet000 facet008 1 ownedP008 (5/8) (3/4) := by
  rcases regime007_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime007_point008_margin0⟩

theorem regime007_mirror11_010_margin0 : (wallDualMargin facet000 facet008 1 mirrorP11_010).BernsteinPosCheck (5/8) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, mirrorP11_010]

theorem regime007_mirror11_010 : WallDualCheck facet000 facet008 1 mirrorP11_010 (5/8) (3/4) := by
  rcases regime007_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime007_mirror11_010_margin0⟩

theorem regime007_mirror11_011_margin0 : (wallDualMargin facet000 facet008 1 mirrorP11_011).BernsteinPosCheck (5/8) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, mirrorP11_011]

theorem regime007_mirror11_011 : WallDualCheck facet000 facet008 1 mirrorP11_011 (5/8) (3/4) := by
  rcases regime007_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime007_mirror11_011_margin0⟩

theorem regime007_point005_dominance : WallProjectionCheck 1 ownedP008 ownedP005 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP005]

theorem regime007_point006_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP006 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP006]

theorem regime007_point007_dominance : WallProjectionCheck 1 mirrorP11_011 ownedP007 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_011, ownedP007]

theorem regime007_point008_dominance : WallProjectionCheck 1 ownedP008 ownedP008 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime007_point010_dominance : WallProjectionCheck 1 ownedP008 ownedP010 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP010]

theorem regime007_point011_dominance : WallProjectionCheck 1 ownedP008 ownedP011 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP011]

theorem regime007_point012_dominance : WallProjectionCheck 1 ownedP008 ownedP012 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP012]

theorem regime007_mirror11_006_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_006 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_006]

theorem regime007_mirror11_007_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_007 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_007]

theorem regime007_mirror11_008_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_008 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_008]

theorem regime007_mirror11_009_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_009 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_009]

theorem regime007_mirror11_010_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_010 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_010]

theorem regime007_mirror11_011_dominance : WallProjectionCheck 1 mirrorP11_011 mirrorP11_011 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_011, mirrorP11_011]

theorem regime007_mirror11_012_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_012 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_012]

theorem regime007_mirror11_013_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_013 (5/8) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_013]

theorem regime007_checked : regime007.Check 4 1 points (5/8) (3/4) := by
  unfold regime007 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact regime007_point008
    · exact regime007_mirror11_010
    · exact regime007_mirror11_011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime007_point005_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime007_point006_dominance⟩
    · exact ⟨mirrorP11_011, by simp, regime007_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_point008_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_point010_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_point011_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_point012_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_mirror11_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_mirror11_007_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_mirror11_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_mirror11_009_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime007_mirror11_010_dominance⟩
    · exact ⟨mirrorP11_011, by simp, regime007_mirror11_011_dominance⟩
    · exact ⟨ownedP008, by simp, regime007_mirror11_012_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime007_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
