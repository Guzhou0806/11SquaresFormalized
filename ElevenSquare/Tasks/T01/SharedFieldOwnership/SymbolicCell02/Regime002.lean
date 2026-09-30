import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime002 : AnchoredWallDirectionCertificate := .crossing facet011 facet015 facet014 (31364411136/40575309727) [ownedP009]

theorem regime002_guard : facet011.determinant facet015 ≠ 0 ∧
    facet015.determinant facet014 ≠ 0 ∧
    0 < (31364411136/40575309727:ℚ) ∧
    wallDualSecondPolynomial facet015 facet014 0 = (wallDualFirstPolynomial facet011 facet015 0).negScale (31364411136/40575309727) ∧
    (wallDualSecondPolynomial facet011 facet015 0).quartic.BernsteinNonnegCheck (1/4) (7/16) ∧
    (wallDualFirstPolynomial facet015 facet014 0).quartic.BernsteinNonnegCheck (1/4) (7/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015, facet014]

theorem regime002_point009_margin0 : (wallDualMargin facet011 facet015 0 ownedP009).BernsteinPosCheck (1/4) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015, facet014, ownedP009]

theorem regime002_point009_margin1 : (wallDualMargin facet015 facet014 0 ownedP009).BernsteinPosCheck (1/4) (7/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015, facet014, ownedP009]

theorem regime002_point009 : WallDualCrossingCheck facet011 facet015 facet014 0 ownedP009 (1/4) (7/16) (31364411136/40575309727) := by
  rcases regime002_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime002_point009_margin0, regime002_point009_margin1⟩

theorem regime002_point005_dominance : WallProjectionCheck 0 ownedP009 ownedP005 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP005]

theorem regime002_point006_dominance : WallProjectionCheck 0 ownedP009 ownedP006 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP006]

theorem regime002_point007_dominance : WallProjectionCheck 0 ownedP009 ownedP007 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime002_point008_dominance : WallProjectionCheck 0 ownedP009 ownedP008 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP008]

theorem regime002_point009_dominance : WallProjectionCheck 0 ownedP009 ownedP009 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime002_mirror13_005_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_005 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_005]

theorem regime002_mirror13_006_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_006 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_006]

theorem regime002_mirror13_007_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_007 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_007]

theorem regime002_mirror13_010_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_010 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_010]

theorem regime002_mirror13_011_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_011 (1/4) (7/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_011]

theorem regime002_checked : regime002.Check 2 0 points (1/4) (7/16) := by
  unfold regime002 AnchoredWallDirectionCertificate.Check
  refine ⟨facet011_mem, facet015_mem, facet014_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime002_point009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP009, by simp, regime002_point005_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_point006_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_point008_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_point009_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_mirror13_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_mirror13_006_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_mirror13_007_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_mirror13_010_dominance⟩
    · exact ⟨ownedP009, by simp, regime002_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
