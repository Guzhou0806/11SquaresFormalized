import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime003 : AnchoredWallDirectionCertificate := .ordinary facet016 facet017 [ownedP010, ownedP011]

theorem regime003_guard : facet016.determinant facet017 ≠ 0 ∧
    (wallDualFirstPolynomial facet016 facet017 0).quartic.BernsteinNonnegCheck (1/2) (5/8) ∧
    (wallDualSecondPolynomial facet016 facet017 0).quartic.BernsteinNonnegCheck (1/2) (5/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet016, facet017]

theorem regime003_point010_margin0 : (wallDualMargin facet016 facet017 0 ownedP010).BernsteinPosCheck (1/2) (5/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet016, facet017, ownedP010]

theorem regime003_point010 : WallDualCheck facet016 facet017 0 ownedP010 (1/2) (5/8) := by
  rcases regime003_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime003_point010_margin0⟩

theorem regime003_point011_margin0 : (wallDualMargin facet016 facet017 0 ownedP011).BernsteinPosCheck (1/2) (5/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet016, facet017, ownedP011]

theorem regime003_point011 : WallDualCheck facet016 facet017 0 ownedP011 (1/2) (5/8) := by
  rcases regime003_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime003_point011_margin0⟩

theorem regime003_point005_dominance : WallProjectionCheck 0 ownedP010 ownedP005 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP005]

theorem regime003_point006_dominance : WallProjectionCheck 0 ownedP010 ownedP006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP006]

theorem regime003_point007_dominance : WallProjectionCheck 0 ownedP010 ownedP007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP007]

theorem regime003_point008_dominance : WallProjectionCheck 0 ownedP010 ownedP008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP008]

theorem regime003_point010_dominance : WallProjectionCheck 0 ownedP010 ownedP010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime003_point011_dominance : WallProjectionCheck 0 ownedP011 ownedP011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime003_point012_dominance : WallProjectionCheck 0 ownedP010 ownedP012 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP012]

theorem regime003_mirror11_006_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_006]

theorem regime003_mirror11_007_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_007]

theorem regime003_mirror11_008_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_008]

theorem regime003_mirror11_009_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_009 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_009]

theorem regime003_mirror11_010_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_010]

theorem regime003_mirror11_011_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_011]

theorem regime003_mirror11_012_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_012 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_012]

theorem regime003_mirror11_013_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_013 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_013]

theorem regime003_checked : regime003.Check 4 0 points (1/2) (5/8) := by
  unfold regime003 AnchoredWallDirectionCertificate.Check
  refine ⟨facet016_mem, facet017_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime003_point010
    · exact regime003_point011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP010, by simp, regime003_point005_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_point006_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_point007_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_point008_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime003_point011_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_point012_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_mirror11_006_dominance⟩
    · exact ⟨ownedP011, by simp, regime003_mirror11_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_mirror11_008_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_mirror11_009_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_mirror11_010_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_mirror11_011_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_mirror11_012_dominance⟩
    · exact ⟨ownedP010, by simp, regime003_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
