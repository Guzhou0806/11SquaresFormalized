import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime011 : AnchoredWallDirectionCertificate := .ordinary facet000 facet016 [ownedP005, mirrorP11_009]

theorem regime011_guard : facet000.determinant facet016 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet016 2).quartic.BernsteinNonnegCheck (1/4) (1) ∧
    (wallDualSecondPolynomial facet000 facet016 2).quartic.BernsteinNonnegCheck (1/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016]

theorem regime011_point005_margin0 : (wallDualMargin facet000 facet016 2 ownedP005).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016, ownedP005]

theorem regime011_point005 : WallDualCheck facet000 facet016 2 ownedP005 (1/4) (1) := by
  rcases regime011_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime011_point005_margin0⟩

theorem regime011_mirror11_009_margin0 : (wallDualMargin facet000 facet016 2 mirrorP11_009).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet016, mirrorP11_009]

theorem regime011_mirror11_009 : WallDualCheck facet000 facet016 2 mirrorP11_009 (1/4) (1) := by
  rcases regime011_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime011_mirror11_009_margin0⟩

theorem regime011_point005_dominance : WallProjectionCheck 2 ownedP005 ownedP005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP005]

theorem regime011_point006_dominance : WallProjectionCheck 2 ownedP005 ownedP006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP006]

theorem regime011_point007_dominance : WallProjectionCheck 2 ownedP005 ownedP007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP007]

theorem regime011_point008_dominance : WallProjectionCheck 2 ownedP005 ownedP008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP008]

theorem regime011_point010_dominance : WallProjectionCheck 2 ownedP005 ownedP010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP010]

theorem regime011_point011_dominance : WallProjectionCheck 2 ownedP005 ownedP011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP011]

theorem regime011_point012_dominance : WallProjectionCheck 2 ownedP005 ownedP012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP012]

theorem regime011_mirror11_006_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_006]

theorem regime011_mirror11_007_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_007]

theorem regime011_mirror11_008_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_008]

theorem regime011_mirror11_009_dominance : WallProjectionCheck 2 mirrorP11_009 mirrorP11_009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_009, mirrorP11_009]

theorem regime011_mirror11_010_dominance : WallProjectionCheck 2 mirrorP11_009 mirrorP11_010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_009, mirrorP11_010]

theorem regime011_mirror11_011_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_011 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_011]

theorem regime011_mirror11_012_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_012 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_012]

theorem regime011_mirror11_013_dominance : WallProjectionCheck 2 ownedP005 mirrorP11_013 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP11_013]

theorem regime011_checked : regime011.Check 4 2 points (1/4) (1) := by
  unfold regime011 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet016_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime011_point005
    · exact regime011_mirror11_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP005, by simp, regime011_point005_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_point006_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_point007_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_point008_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_point010_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_point011_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_point012_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_mirror11_006_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_mirror11_007_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_mirror11_008_dominance⟩
    · exact ⟨mirrorP11_009, by simp, regime011_mirror11_009_dominance⟩
    · exact ⟨mirrorP11_009, by simp, regime011_mirror11_010_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_mirror11_011_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_mirror11_012_dominance⟩
    · exact ⟨ownedP005, by simp, regime011_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
