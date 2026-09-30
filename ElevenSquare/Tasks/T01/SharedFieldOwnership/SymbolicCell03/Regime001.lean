import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime001 : AnchoredWallDirectionCertificate := .ordinary facet001 facet015 [ownedP009, ownedP010]

theorem regime001_guard : facet001.determinant facet015 ≠ 0 ∧
    (wallDualFirstPolynomial facet001 facet015 0).quartic.BernsteinNonnegCheck (1/2) (5/8) ∧
    (wallDualSecondPolynomial facet001 facet015 0).quartic.BernsteinNonnegCheck (1/2) (5/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015]

theorem regime001_point009_margin0 : (wallDualMargin facet001 facet015 0 ownedP009).BernsteinPosCheck (1/2) (5/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015, ownedP009]

theorem regime001_point009 : WallDualCheck facet001 facet015 0 ownedP009 (1/2) (5/8) := by
  rcases regime001_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime001_point009_margin0⟩

theorem regime001_point010_margin0 : (wallDualMargin facet001 facet015 0 ownedP010).BernsteinPosCheck (1/2) (5/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet001, facet015, ownedP010]

theorem regime001_point010 : WallDualCheck facet001 facet015 0 ownedP010 (1/2) (5/8) := by
  rcases regime001_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime001_point010_margin0⟩

theorem regime001_point005_dominance : WallProjectionCheck 0 ownedP009 ownedP005 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP005]

theorem regime001_point006_dominance : WallProjectionCheck 0 ownedP009 ownedP006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP006]

theorem regime001_point007_dominance : WallProjectionCheck 0 ownedP009 ownedP007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime001_point008_dominance : WallProjectionCheck 0 ownedP009 ownedP008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP008]

theorem regime001_point009_dominance : WallProjectionCheck 0 ownedP009 ownedP009 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime001_point010_dominance : WallProjectionCheck 0 ownedP010 ownedP010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime001_point011_dominance : WallProjectionCheck 0 ownedP009 ownedP011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP011]

theorem regime001_mirror12_005_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_005 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_005]

theorem regime001_mirror12_006_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_006]

theorem regime001_mirror12_007_dominance : WallProjectionCheck 0 ownedP010 mirrorP12_007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP12_007]

theorem regime001_mirror12_008_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_008]

theorem regime001_mirror12_009_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_009 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_009]

theorem regime001_mirror12_010_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_010]

theorem regime001_mirror12_011_dominance : WallProjectionCheck 0 ownedP009 mirrorP12_011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP12_011]

theorem regime001_checked : regime001.Check 3 0 points (1/2) (5/8) := by
  unfold regime001 AnchoredWallDirectionCertificate.Check
  refine ⟨facet001_mem, facet015_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime001_point009
    · exact regime001_point010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP009, by simp, regime001_point005_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point006_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point008_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point009_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_point010_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_point011_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror12_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror12_006_dominance⟩
    · exact ⟨ownedP010, by simp, regime001_mirror12_007_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror12_008_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror12_009_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror12_010_dominance⟩
    · exact ⟨ownedP009, by simp, regime001_mirror12_011_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
