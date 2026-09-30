import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime004 : AnchoredWallDirectionCertificate := .crossing facet017 facet016 facet000 (271974970539/528190000000) [ownedP011]

theorem regime004_guard : facet017.determinant facet016 ≠ 0 ∧
    facet016.determinant facet000 ≠ 0 ∧
    0 < (271974970539/528190000000:ℚ) ∧
    wallDualSecondPolynomial facet016 facet000 0 = (wallDualFirstPolynomial facet017 facet016 0).negScale (271974970539/528190000000) ∧
    (wallDualSecondPolynomial facet017 facet016 0).quartic.BernsteinNonnegCheck (5/8) (1) ∧
    (wallDualFirstPolynomial facet016 facet000 0).quartic.BernsteinNonnegCheck (5/8) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet017, facet016, facet000]

theorem regime004_point011_margin0 : (wallDualMargin facet017 facet016 0 ownedP011).BernsteinPosCheck (5/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet017, facet016, facet000, ownedP011]

theorem regime004_point011_margin1 : (wallDualMargin facet016 facet000 0 ownedP011).BernsteinPosCheck (5/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet017, facet016, facet000, ownedP011]

theorem regime004_point011 : WallDualCrossingCheck facet017 facet016 facet000 0 ownedP011 (5/8) (1) (271974970539/528190000000) := by
  rcases regime004_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime004_point011_margin0, regime004_point011_margin1⟩

theorem regime004_point005_dominance : WallProjectionCheck 0 ownedP011 ownedP005 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP005]

theorem regime004_point006_dominance : WallProjectionCheck 0 ownedP011 ownedP006 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP006]

theorem regime004_point007_dominance : WallProjectionCheck 0 ownedP011 ownedP007 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP007]

theorem regime004_point008_dominance : WallProjectionCheck 0 ownedP011 ownedP008 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP008]

theorem regime004_point010_dominance : WallProjectionCheck 0 ownedP011 ownedP010 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP010]

theorem regime004_point011_dominance : WallProjectionCheck 0 ownedP011 ownedP011 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP011]

theorem regime004_point012_dominance : WallProjectionCheck 0 ownedP011 ownedP012 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, ownedP012]

theorem regime004_mirror11_006_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_006 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_006]

theorem regime004_mirror11_007_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_007 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_007]

theorem regime004_mirror11_008_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_008 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_008]

theorem regime004_mirror11_009_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_009 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_009]

theorem regime004_mirror11_010_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_010 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_010]

theorem regime004_mirror11_011_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_011 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_011]

theorem regime004_mirror11_012_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_012 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_012]

theorem regime004_mirror11_013_dominance : WallProjectionCheck 0 ownedP011 mirrorP11_013 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP011, mirrorP11_013]

theorem regime004_checked : regime004.Check 4 0 points (5/8) (1) := by
  unfold regime004 AnchoredWallDirectionCertificate.Check
  refine ⟨facet017_mem, facet016_mem, facet000_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime004_point011
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP011, by simp, regime004_point005_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_point006_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_point007_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_point008_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_point010_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_point011_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_point012_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_006_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_007_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_008_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_009_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_010_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_011_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_012_dominance⟩
    · exact ⟨ownedP011, by simp, regime004_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
