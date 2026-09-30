import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime002 : AnchoredWallDirectionCertificate := .crossing facet001 facet015 facet010 (86578125/40839077) [ownedP010]

theorem regime002_guard : facet001.determinant facet015 ≠ 0 ∧
    facet015.determinant facet010 ≠ 0 ∧
    0 < (86578125/40839077:ℚ) ∧
    wallDualSecondPolynomial facet015 facet010 0 = (wallDualFirstPolynomial facet001 facet015 0).negScale (86578125/40839077) ∧
    (wallDualSecondPolynomial facet001 facet015 0).quartic.BernsteinNonnegCheck (5/8) (1) ∧
    (wallDualFirstPolynomial facet015 facet010 0).quartic.BernsteinNonnegCheck (5/8) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015, facet010]

theorem regime002_point010_margin0 : (wallDualMargin facet001 facet015 0 ownedP010).BernsteinPosCheck (5/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015, facet010, ownedP010]

theorem regime002_point010_margin1 : (wallDualMargin facet015 facet010 0 ownedP010).BernsteinPosCheck (5/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015, facet010, ownedP010]

theorem regime002_point010 : WallDualCrossingCheck facet001 facet015 facet010 0 ownedP010 (5/8) (1) (86578125/40839077) := by
  rcases regime002_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime002_point010_margin0, regime002_point010_margin1⟩

theorem regime002_point005_dominance : WallProjectionCheck 0 ownedP010 ownedP005 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP005]

theorem regime002_point006_dominance : WallProjectionCheck 0 ownedP010 ownedP006 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP006]

theorem regime002_point007_dominance : WallProjectionCheck 0 ownedP010 ownedP007 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP007]

theorem regime002_point008_dominance : WallProjectionCheck 0 ownedP010 ownedP008 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP008]

theorem regime002_point009_dominance : WallProjectionCheck 0 ownedP010 ownedP009 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP009]

theorem regime002_point010_dominance : WallProjectionCheck 0 ownedP010 ownedP010 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime002_point011_dominance : WallProjectionCheck 0 ownedP010 ownedP011 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP011]

theorem regime002_mirror12_005_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_005 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_005]

theorem regime002_mirror12_006_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_006 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_006]

theorem regime002_mirror12_007_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_007 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_007]

theorem regime002_mirror12_008_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_008 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_008]

theorem regime002_mirror12_009_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_009 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_009]

theorem regime002_mirror12_010_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_010 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_010]

theorem regime002_mirror12_011_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_011 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_011]

theorem regime002_checked : regime002.Check 3 0 points (5/8) (1) := by
  unfold regime002 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet015_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime002_point010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP010, by simp, regime002_point005_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_point006_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_point007_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_point008_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_point009_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_point010_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_point011_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_mirror12_005_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_mirror12_006_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_mirror12_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_mirror12_008_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_mirror12_009_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_mirror12_010_dominance⟩
    · exact ⟨ownedP010, by simp, regime002_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
