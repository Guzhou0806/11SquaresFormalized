import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime004 : AnchoredWallDirectionCertificate := .ordinary facet002 facet008 [mirrorP14_009]

theorem regime004_guard : facet002.determinant facet008 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet008 1).quartic.BernsteinNonnegCheck (1/8) (1) ∧
    (wallDualSecondPolynomial facet002 facet008 1).quartic.BernsteinNonnegCheck (1/8) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet008]

theorem regime004_mirror14_009_margin0 : (wallDualMargin facet002 facet008 1 mirrorP14_009).BernsteinPosCheck (1/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet008, mirrorP14_009]

theorem regime004_mirror14_009 : WallDualCheck facet002 facet008 1 mirrorP14_009 (1/8) (1) := by
  rcases regime004_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime004_mirror14_009_margin0⟩

theorem regime004_point005_dominance : WallProjectionCheck 1 mirrorP14_009 ownedP005 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, ownedP005]

theorem regime004_point006_dominance : WallProjectionCheck 1 mirrorP14_009 ownedP006 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, ownedP006]

theorem regime004_point007_dominance : WallProjectionCheck 1 mirrorP14_009 ownedP007 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, ownedP007]

theorem regime004_point008_dominance : WallProjectionCheck 1 mirrorP14_009 ownedP008 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, ownedP008]

theorem regime004_mirror14_005_dominance : WallProjectionCheck 1 mirrorP14_009 mirrorP14_005 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, mirrorP14_005]

theorem regime004_mirror14_006_dominance : WallProjectionCheck 1 mirrorP14_009 mirrorP14_006 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, mirrorP14_006]

theorem regime004_mirror14_008_dominance : WallProjectionCheck 1 mirrorP14_009 mirrorP14_008 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, mirrorP14_008]

theorem regime004_mirror14_009_dominance : WallProjectionCheck 1 mirrorP14_009 mirrorP14_009 (1/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, mirrorP14_009]

theorem regime004_checked : regime004.Check 1 1 points (1/8) (1) := by
  unfold regime004 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime004_mirror14_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP14_009, by simp, regime004_point005_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime004_point006_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime004_point007_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime004_point008_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime004_mirror14_005_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime004_mirror14_006_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime004_mirror14_008_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime004_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
