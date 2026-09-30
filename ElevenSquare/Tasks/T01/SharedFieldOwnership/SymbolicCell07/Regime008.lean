import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime008 : AnchoredWallDirectionCertificate := .crossing facet010 facet011 facet001 (40839077/86578125) [ownedP008]

theorem regime008_guard : facet010.determinant facet011 ≠ 0 ∧
    facet011.determinant facet001 ≠ 0 ∧
    0 < (40839077/86578125:ℚ) ∧
    wallDualSecondPolynomial facet011 facet001 1 = (wallDualFirstPolynomial facet010 facet011 1).negScale (40839077/86578125) ∧
    (wallDualSecondPolynomial facet010 facet011 1).quartic.BernsteinNonnegCheck (1/2) (1) ∧
    (wallDualFirstPolynomial facet011 facet001 1).quartic.BernsteinNonnegCheck (1/2) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet011, facet001]

theorem regime008_point008_margin0 : (wallDualMargin facet010 facet011 1 ownedP008).BernsteinPosCheck (1/2) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet011, facet001, ownedP008]

theorem regime008_point008_margin1 : (wallDualMargin facet011 facet001 1 ownedP008).BernsteinPosCheck (1/2) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet011, facet001, ownedP008]

theorem regime008_point008 : WallDualCrossingCheck facet010 facet011 facet001 1 ownedP008 (1/2) (1) (40839077/86578125) := by
  rcases regime008_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime008_point008_margin0, regime008_point008_margin1⟩

theorem regime008_point006_dominance : WallProjectionCheck 1 ownedP008 ownedP006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime008_point007_dominance : WallProjectionCheck 1 ownedP008 ownedP007 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime008_point008_dominance : WallProjectionCheck 1 ownedP008 ownedP008 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime008_point009_dominance : WallProjectionCheck 1 ownedP008 ownedP009 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP009]

theorem regime008_point010_dominance : WallProjectionCheck 1 ownedP008 ownedP010 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP010]

theorem regime008_point011_dominance : WallProjectionCheck 1 ownedP008 ownedP011 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP011]

theorem regime008_point012_dominance : WallProjectionCheck 1 ownedP008 ownedP012 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP012]

theorem regime008_point013_dominance : WallProjectionCheck 1 ownedP008 ownedP013 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP013]

theorem regime008_point014_dominance : WallProjectionCheck 1 ownedP008 ownedP014 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP014]

theorem regime008_mirror08_005_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_005 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_005]

theorem regime008_mirror08_006_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_006]

theorem regime008_mirror08_007_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_007 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_007]

theorem regime008_mirror08_008_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_008 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_008]

theorem regime008_mirror08_010_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_010 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_010]

theorem regime008_mirror08_011_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_011 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_011]

theorem regime008_mirror08_012_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_012 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_012]

theorem regime008_mirror08_013_dominance : WallProjectionCheck 1 ownedP008 mirrorP08_013 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP08_013]

theorem regime008_checked : regime008.Check 7 1 points (1/2) (1) := by
  unfold regime008 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet011_mem, facet001_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime008_point008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime008_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point008_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point009_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point010_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point011_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point012_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point013_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point014_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_007_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_010_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_011_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_012_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror08_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
