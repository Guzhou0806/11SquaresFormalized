import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime001 : AnchoredWallDirectionCertificate := .crossing facet013 facet017 facet016 (32043020630/30219441171) [ownedP010]

theorem regime001_guard : facet013.determinant facet017 ≠ 0 ∧
    facet017.determinant facet016 ≠ 0 ∧
    0 < (32043020630/30219441171:ℚ) ∧
    wallDualSecondPolynomial facet017 facet016 0 = (wallDualFirstPolynomial facet013 facet017 0).negScale (32043020630/30219441171) ∧
    (wallDualSecondPolynomial facet013 facet017 0).quartic.BernsteinNonnegCheck (5/32) (3/8) ∧
    (wallDualFirstPolynomial facet017 facet016 0).quartic.BernsteinNonnegCheck (5/32) (3/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet017, facet016]

theorem regime001_point010_margin0 : (wallDualMargin facet013 facet017 0 ownedP010).BernsteinPosCheck (5/32) (3/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet017, facet016, ownedP010]

theorem regime001_point010_margin1 : (wallDualMargin facet017 facet016 0 ownedP010).BernsteinPosCheck (5/32) (3/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet013, facet017, facet016, ownedP010]

theorem regime001_point010 : WallDualCrossingCheck facet013 facet017 facet016 0 ownedP010 (5/32) (3/8) (32043020630/30219441171) := by
  rcases regime001_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime001_point010_margin0, regime001_point010_margin1⟩

theorem regime001_point005_dominance : WallProjectionCheck 0 ownedP010 ownedP005 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP005]

theorem regime001_point006_dominance : WallProjectionCheck 0 ownedP010 ownedP006 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP006]

theorem regime001_point007_dominance : WallProjectionCheck 0 ownedP010 ownedP007 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP007]

theorem regime001_point008_dominance : WallProjectionCheck 0 ownedP010 ownedP008 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP008]

theorem regime001_point010_dominance : WallProjectionCheck 0 ownedP010 ownedP010 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime001_point011_dominance : WallProjectionCheck 0 ownedP010 ownedP011 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP011]

theorem regime001_point012_dominance : WallProjectionCheck 0 ownedP010 ownedP012 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP012]

theorem regime001_mirror11_006_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_006 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_006]

theorem regime001_mirror11_007_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_007 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_007]

theorem regime001_mirror11_008_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_008 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_008]

theorem regime001_mirror11_009_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_009 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_009]

theorem regime001_mirror11_010_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_010 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_010]

theorem regime001_mirror11_011_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_011 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_011]

theorem regime001_mirror11_012_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_012 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_012]

theorem regime001_mirror11_013_dominance : WallProjectionCheck 0 ownedP010 mirrorP11_013 (5/32) (3/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP11_013]

theorem regime001_checked : regime001.Check 4 0 points (5/32) (3/8) := by
  unfold regime001 AnchoredWallDirectionCertificate.Check
  refine ⟨facet013_mem, facet017_mem, facet016_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime001_point010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP010, by simp, regime001_point005_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_point006_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_point007_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_point008_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_point010_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_point011_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_point012_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_006_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_008_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_009_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_010_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_011_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_012_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
