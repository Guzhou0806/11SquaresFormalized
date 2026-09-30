import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime002 : AnchoredWallDirectionCertificate := .ordinary facet010 facet013 [ownedP008]

theorem regime002_guard : facet010.determinant facet013 ≠ 0 ∧
    (wallDualFirstPolynomial facet010 facet013 0).quartic.BernsteinNonnegCheck (1/2) (1) ∧
    (wallDualSecondPolynomial facet010 facet013 0).quartic.BernsteinNonnegCheck (1/2) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet013]

theorem regime002_point008_margin0 : (wallDualMargin facet010 facet013 0 ownedP008).BernsteinPosCheck (1/2) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet010, facet013, ownedP008]

theorem regime002_point008 : WallDualCheck facet010 facet013 0 ownedP008 (1/2) (1) := by
  rcases regime002_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime002_point008_margin0⟩

theorem regime002_point005_dominance : WallProjectionCheck 0 ownedP008 ownedP005 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP005]

theorem regime002_point006_dominance : WallProjectionCheck 0 ownedP008 ownedP006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime002_point007_dominance : WallProjectionCheck 0 ownedP008 ownedP007 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime002_point008_dominance : WallProjectionCheck 0 ownedP008 ownedP008 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime002_mirror14_005_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_005 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_005]

theorem regime002_mirror14_006_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_006 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_006]

theorem regime002_mirror14_008_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_008 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_008]

theorem regime002_mirror14_009_dominance : WallProjectionCheck 0 ownedP008 mirrorP14_009 (1/2) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP14_009]

theorem regime002_checked : regime002.Check 1 0 points (1/2) (1) := by
  unfold regime002 AnchoredWallDirectionCertificate.Check
  refine ⟨facet010_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime002_point008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime002_point005_dominance⟩
    · exact ⟨ownedP008, by simp, regime002_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime002_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime002_point008_dominance⟩
    · exact ⟨ownedP008, by simp, regime002_mirror14_005_dominance⟩
    · exact ⟨ownedP008, by simp, regime002_mirror14_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime002_mirror14_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime002_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
