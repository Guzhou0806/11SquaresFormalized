import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime001 : AnchoredWallDirectionCertificate := .ordinary facet011 facet015 [ownedP008, ownedP009]

theorem regime001_guard : facet011.determinant facet015 ≠ 0 ∧
    (wallDualFirstPolynomial facet011 facet015 0).quartic.BernsteinNonnegCheck (3/16) (1/4) ∧
    (wallDualSecondPolynomial facet011 facet015 0).quartic.BernsteinNonnegCheck (3/16) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015]

theorem regime001_point008_margin0 : (wallDualMargin facet011 facet015 0 ownedP008).BernsteinPosCheck (3/16) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015, ownedP008]

theorem regime001_point008 : WallDualCheck facet011 facet015 0 ownedP008 (3/16) (1/4) := by
  rcases regime001_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime001_point008_margin0⟩

theorem regime001_point009_margin0 : (wallDualMargin facet011 facet015 0 ownedP009).BernsteinPosCheck (3/16) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet011, facet015, ownedP009]

theorem regime001_point009 : WallDualCheck facet011 facet015 0 ownedP009 (3/16) (1/4) := by
  rcases regime001_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime001_point009_margin0⟩

theorem regime001_point005_dominance : WallProjectionCheck 0 ownedP008 ownedP005 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP005]

theorem regime001_point006_dominance : WallProjectionCheck 0 ownedP008 ownedP006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime001_point007_dominance : WallProjectionCheck 0 ownedP008 ownedP007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime001_point008_dominance : WallProjectionCheck 0 ownedP008 ownedP008 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime001_point009_dominance : WallProjectionCheck 0 ownedP009 ownedP009 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime001_mirror13_005_dominance : WallProjectionCheck 0 ownedP008 mirrorP13_005 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP13_005]

theorem regime001_mirror13_006_dominance : WallProjectionCheck 0 ownedP008 mirrorP13_006 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP13_006]

theorem regime001_mirror13_007_dominance : WallProjectionCheck 0 ownedP009 mirrorP13_007 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP13_007]

theorem regime001_mirror13_010_dominance : WallProjectionCheck 0 ownedP008 mirrorP13_010 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP13_010]

theorem regime001_mirror13_011_dominance : WallProjectionCheck 0 ownedP008 mirrorP13_011 (3/16) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP13_011]

theorem regime001_checked : regime001.Check 2 0 points (3/16) (1/4) := by
  unfold regime001 AnchoredWallDirectionCertificate.Check
  refine ⟨facet011_mem, facet015_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime001_point008
    · exact regime001_point009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime001_point005_dominance⟩
    · exact ⟨ownedP008, by simp, regime001_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime001_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime001_point008_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point009_dominance⟩
    · exact ⟨ownedP008, by simp, regime001_mirror13_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime001_mirror13_006_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror13_007_dominance⟩
    · exact ⟨ownedP008, by simp, regime001_mirror13_010_dominance⟩
    · exact ⟨ownedP008, by simp, regime001_mirror13_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
