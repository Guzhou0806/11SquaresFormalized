import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime010 : AnchoredWallDirectionCertificate := .ordinary facet000 facet016 [ownedP005, ownedP011, ownedP012]

theorem regime010_guard : facet000.determinant facet016 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet016 2).quartic.BernsteinNonnegCheck (1/8) (1/4) ∧
    (wallDualSecondPolynomial facet000 facet016 2).quartic.BernsteinNonnegCheck (1/8) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016]

theorem regime010_point005_margin0 : (wallDualMargin facet000 facet016 2 ownedP005).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016, ownedP005]

theorem regime010_point005 : WallDualCheck facet000 facet016 2 ownedP005 (1/8) (1/4) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point005_margin0⟩

theorem regime010_point011_margin0 : (wallDualMargin facet000 facet016 2 ownedP011).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016, ownedP011]

theorem regime010_point011 : WallDualCheck facet000 facet016 2 ownedP011 (1/8) (1/4) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point011_margin0⟩

theorem regime010_point012_margin0 : (wallDualMargin facet000 facet016 2 ownedP012).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016, ownedP012]

theorem regime010_point012 : WallDualCheck facet000 facet016 2 ownedP012 (1/8) (1/4) := by
  rcases regime010_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime010_point012_margin0⟩

theorem regime010_point005_dominance : WallProjectionCheck 2 ownedP005 ownedP005 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP005]

theorem regime010_point006_dominance : WallProjectionCheck 2 ownedP005 ownedP006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP006]

theorem regime010_point007_dominance : WallProjectionCheck 2 ownedP005 ownedP007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP007]

theorem regime010_point008_dominance : WallProjectionCheck 2 ownedP005 ownedP008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP008]

theorem regime010_point010_dominance : WallProjectionCheck 2 ownedP005 ownedP010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP010]

theorem regime010_point011_dominance : WallProjectionCheck 2 ownedP011 ownedP011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime010_point012_dominance : WallProjectionCheck 2 ownedP012 ownedP012 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP012, ownedP012]

theorem regime010_mirror11_006_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_006]

theorem regime010_mirror11_007_dominance : WallProjectionCheck 2 ownedP011 mirrorP11_007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_007]

theorem regime010_mirror11_008_dominance : WallProjectionCheck 2 ownedP012 mirrorP11_008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP012, mirrorP11_008]

theorem regime010_mirror11_009_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_009 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_009]

theorem regime010_mirror11_010_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_010]

theorem regime010_mirror11_011_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_011]

theorem regime010_mirror11_012_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_012 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_012]

theorem regime010_mirror11_013_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_013 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_013]

theorem regime010_checked : regime010.Check 4 2 points (1/8) (1/4) := by
  unfold regime010 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet016_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact regime010_point005
    · exact regime010_point011
    · exact regime010_point012
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP005, by simp, regime010_point005_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_point006_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_point007_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_point008_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime010_point011_dominance⟩
    · exact ⟨ownedP012, by simp, regime010_point012_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_mirror11_006_dominance⟩
    · exact ⟨ownedP011, by simp, regime010_mirror11_007_dominance⟩
    · exact ⟨ownedP012, by simp, regime010_mirror11_008_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_mirror11_009_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_mirror11_010_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_mirror11_011_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_mirror11_012_dominance⟩
    · exact ⟨ownedP005, by simp, regime010_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
