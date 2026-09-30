import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime006 : AnchoredWallDirectionCertificate := .ordinary facet008 facet013 [ownedP005, mirrorP14_008]

theorem regime006_guard : facet008.determinant facet013 ≠ 0 ∧
    (wallDualFirstPolynomial facet008 facet013 2).quartic.BernsteinNonnegCheck (3/8) (1/2) ∧
    (wallDualSecondPolynomial facet008 facet013 2).quartic.BernsteinNonnegCheck (3/8) (1/2) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013]

theorem regime006_point005_margin0 : (wallDualMargin facet008 facet013 2 ownedP005).BernsteinPosCheck (3/8) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, ownedP005]

theorem regime006_point005 : WallDualCheck facet008 facet013 2 ownedP005 (3/8) (1/2) := by
  rcases regime006_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime006_point005_margin0⟩

theorem regime006_mirror14_008_margin0 : (wallDualMargin facet008 facet013 2 mirrorP14_008).BernsteinPosCheck (3/8) (1/2) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, mirrorP14_008]

theorem regime006_mirror14_008 : WallDualCheck facet008 facet013 2 mirrorP14_008 (3/8) (1/2) := by
  rcases regime006_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime006_mirror14_008_margin0⟩

theorem regime006_point005_dominance : WallProjectionCheck 2 ownedP005 ownedP005 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP005]

theorem regime006_point006_dominance : WallProjectionCheck 2 ownedP005 ownedP006 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP006]

theorem regime006_point007_dominance : WallProjectionCheck 2 ownedP005 ownedP007 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP007]

theorem regime006_point008_dominance : WallProjectionCheck 2 ownedP005 ownedP008 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP008]

theorem regime006_mirror14_005_dominance : WallProjectionCheck 2 ownedP005 mirrorP14_005 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP14_005]

theorem regime006_mirror14_006_dominance : WallProjectionCheck 2 ownedP005 mirrorP14_006 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP14_006]

theorem regime006_mirror14_008_dominance : WallProjectionCheck 2 mirrorP14_008 mirrorP14_008 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_008]

theorem regime006_mirror14_009_dominance : WallProjectionCheck 2 ownedP005 mirrorP14_009 (3/8) (1/2) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP14_009]

theorem regime006_checked : regime006.Check 1 2 points (3/8) (1/2) := by
  unfold regime006 AnchoredWallDirectionCertificate.Check
  refine ⟨facet008_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime006_point005
    · exact regime006_mirror14_008
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP005, by simp, regime006_point005_dominance⟩
    · exact ⟨ownedP005, by simp, regime006_point006_dominance⟩
    · exact ⟨ownedP005, by simp, regime006_point007_dominance⟩
    · exact ⟨ownedP005, by simp, regime006_point008_dominance⟩
    · exact ⟨ownedP005, by simp, regime006_mirror14_005_dominance⟩
    · exact ⟨ownedP005, by simp, regime006_mirror14_006_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime006_mirror14_008_dominance⟩
    · exact ⟨ownedP005, by simp, regime006_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
