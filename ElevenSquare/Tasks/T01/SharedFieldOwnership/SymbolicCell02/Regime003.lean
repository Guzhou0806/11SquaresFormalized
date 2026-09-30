import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime003 : AnchoredWallDirectionCertificate := .crossing facet015 facet014 facet000 (40575309727/79219000000) [ownedP009]

theorem regime003_guard : facet015.determinant facet014 ≠ 0 ∧
    facet014.determinant facet000 ≠ 0 ∧
    0 < (40575309727/79219000000:ℚ) ∧
    wallDualSecondPolynomial facet014 facet000 0 = (wallDualFirstPolynomial facet015 facet014 0).negScale (40575309727/79219000000) ∧
    (wallDualSecondPolynomial facet015 facet014 0).quartic.BernsteinNonnegCheck (7/16) (1) ∧
    (wallDualFirstPolynomial facet014 facet000 0).quartic.BernsteinNonnegCheck (7/16) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet015, facet014, facet000]

theorem regime003_point009_margin0 : (wallDualMargin facet015 facet014 0 ownedP009).BernsteinPosCheck (7/16) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet015, facet014, facet000, ownedP009]

theorem regime003_point009_margin1 : (wallDualMargin facet014 facet000 0 ownedP009).BernsteinPosCheck (7/16) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet015, facet014, facet000, ownedP009]

theorem regime003_point009 : WallDualCrossingCheck facet015 facet014 facet000 0 ownedP009 (7/16) (1) (40575309727/79219000000) := by
  rcases regime003_guard with ⟨hfg, hgh, hr, heq, hleft, hright⟩
  exact ⟨hfg, hgh, hr, heq, hleft, hright, regime003_point009_margin0, regime003_point009_margin1⟩

theorem regime003_point005_dominance : WallProjectionCheck 0 ownedP009 ownedP005 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP005]

theorem regime003_point006_dominance : WallProjectionCheck 0 ownedP009 ownedP006 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP006]

theorem regime003_point007_dominance : WallProjectionCheck 0 ownedP009 ownedP007 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime003_point008_dominance : WallProjectionCheck 0 ownedP009 ownedP008 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP008]

theorem regime003_point009_dominance : WallProjectionCheck 0 ownedP009 ownedP009 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime003_mirror13_005_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_005 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_005]

theorem regime003_mirror13_006_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_006 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_006]

theorem regime003_mirror13_007_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_007 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_007]

theorem regime003_mirror13_010_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_010 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_010]

theorem regime003_mirror13_011_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_011 (7/16) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_011]

theorem regime003_checked : regime003.Check 2 0 points (7/16) (1) := by
  unfold regime003 AnchoredWallDirectionCertificate.Check
  refine ⟨facet015_mem, facet014_mem, facet000_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime003_point009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP009, by simp, regime003_point005_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_point006_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_point008_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_point009_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror13_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror13_006_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror13_007_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror13_010_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
