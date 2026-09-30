import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime003 : AnchoredWallDirectionCertificate := .ordinary facet002 facet008 [mirrorP14_008, mirrorP14_009]

theorem regime003_guard : facet002.determinant facet008 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet008 1).quartic.BernsteinNonnegCheck (0) (1/8) ∧
    (wallDualSecondPolynomial facet002 facet008 1).quartic.BernsteinNonnegCheck (0) (1/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet008]

theorem regime003_mirror14_008_margin0 : (wallDualMargin facet002 facet008 1 mirrorP14_008).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet008, mirrorP14_008]

theorem regime003_mirror14_008 : WallDualCheck facet002 facet008 1 mirrorP14_008 (0) (1/8) := by
  rcases regime003_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime003_mirror14_008_margin0⟩

theorem regime003_mirror14_009_margin0 : (wallDualMargin facet002 facet008 1 mirrorP14_009).BernsteinPosCheck (0) (1/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet008, mirrorP14_009]

theorem regime003_mirror14_009 : WallDualCheck facet002 facet008 1 mirrorP14_009 (0) (1/8) := by
  rcases regime003_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime003_mirror14_009_margin0⟩

theorem regime003_point005_dominance : WallProjectionCheck 1 mirrorP14_008 ownedP005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, ownedP005]

theorem regime003_point006_dominance : WallProjectionCheck 1 mirrorP14_009 ownedP006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, ownedP006]

theorem regime003_point007_dominance : WallProjectionCheck 1 mirrorP14_008 ownedP007 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, ownedP007]

theorem regime003_point008_dominance : WallProjectionCheck 1 mirrorP14_008 ownedP008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, ownedP008]

theorem regime003_mirror14_005_dominance : WallProjectionCheck 1 mirrorP14_008 mirrorP14_005 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_005]

theorem regime003_mirror14_006_dominance : WallProjectionCheck 1 mirrorP14_008 mirrorP14_006 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_006]

theorem regime003_mirror14_008_dominance : WallProjectionCheck 1 mirrorP14_008 mirrorP14_008 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_008, mirrorP14_008]

theorem regime003_mirror14_009_dominance : WallProjectionCheck 1 mirrorP14_009 mirrorP14_009 (0) (1/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, mirrorP14_009]

theorem regime003_checked : regime003.Check 1 1 points (0) (1/8) := by
  unfold regime003 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime003_mirror14_008
    · exact regime003_mirror14_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP14_008, by simp, regime003_point005_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime003_point006_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime003_point007_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime003_point008_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime003_mirror14_005_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime003_mirror14_006_dominance⟩
    · exact ⟨mirrorP14_008, by simp, regime003_mirror14_008_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime003_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
