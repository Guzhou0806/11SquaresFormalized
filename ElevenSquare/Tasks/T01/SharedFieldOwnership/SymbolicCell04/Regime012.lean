import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime012 : AnchoredWallDirectionCertificate := .crossing facet000 facet008 facet013 (89153500000/47687071873) [mirrorP11_012]

theorem regime012_guard : facet000.determinant facet008 ≠ 0 ∧
    facet008.determinant facet013 ≠ 0 ∧
    0 < (89153500000/47687071873:ℚ) ∧
    wallDualSecondPolynomial facet008 facet013 3 = (wallDualFirstPolynomial facet000 facet008 3).negScale (89153500000/47687071873) ∧
    (wallDualSecondPolynomial facet000 facet008 3).quartic.BernsteinNonnegCheck (0) (1/8) ∧
    (wallDualFirstPolynomial facet008 facet013 3).quartic.BernsteinNonnegCheck (0) (1/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, facet013]

theorem regime012_mirror11_012_margin0 : (wallDualMargin facet000 facet008 3 mirrorP11_012).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, facet013, mirrorP11_012]

theorem regime012_mirror11_012_margin1 : (wallDualMargin facet008 facet013 3 mirrorP11_012).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, facet013, mirrorP11_012]

theorem regime012_mirror11_012 : WallDualCrossingCheck facet000 facet008 facet013 3 mirrorP11_012 (0) (1/8) (89153500000/47687071873) := by
  rcases regime012_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime012_mirror11_012_margin0, regime012_mirror11_012_margin1⟩

theorem regime012_point005_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP005]

theorem regime012_point006_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP006]

theorem regime012_point007_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP007]

theorem regime012_point008_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP008]

theorem regime012_point010_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP010]

theorem regime012_point011_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP011]

theorem regime012_point012_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP012 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP012]

theorem regime012_mirror11_006_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_006]

theorem regime012_mirror11_007_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_007]

theorem regime012_mirror11_008_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_008]

theorem regime012_mirror11_009_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_009]

theorem regime012_mirror11_010_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_010 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_010]

theorem regime012_mirror11_011_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_011 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_011]

theorem regime012_mirror11_012_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_012 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_012]

theorem regime012_mirror11_013_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_013 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_013]

theorem regime012_checked : regime012.Check 4 3 points (0) (1/8) := by
  unfold regime012 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet008_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime012_mirror11_012
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP11_012, by simp, regime012_point005_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_point006_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_point007_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_point008_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_point010_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_point011_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_point012_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_006_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_007_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_008_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_009_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_010_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_011_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_012_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime012_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
