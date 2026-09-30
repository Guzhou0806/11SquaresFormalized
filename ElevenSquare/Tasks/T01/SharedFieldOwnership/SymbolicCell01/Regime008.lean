import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime008 : AnchoredWallDirectionCertificate := .ordinary facet002 facet010 [ownedP006, mirrorP14_009]

theorem regime008_guard : facet002.determinant facet010 ≠ 0 ∧
    (wallDualFirstPolynomial facet002 facet010 3).quartic.BernsteinNonnegCheck (0) (3/4) ∧
    (wallDualSecondPolynomial facet002 facet010 3).quartic.BernsteinNonnegCheck (0) (3/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010]

theorem regime008_point006_margin0 : (wallDualMargin facet002 facet010 3 ownedP006).BernsteinPosCheck (0) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, ownedP006]

theorem regime008_point006 : WallDualCheck facet002 facet010 3 ownedP006 (0) (3/4) := by
  rcases regime008_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime008_point006_margin0⟩

theorem regime008_mirror14_009_margin0 : (wallDualMargin facet002 facet010 3 mirrorP14_009).BernsteinPosCheck (0) (3/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet002, facet010, mirrorP14_009]

theorem regime008_mirror14_009 : WallDualCheck facet002 facet010 3 mirrorP14_009 (0) (3/4) := by
  rcases regime008_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime008_mirror14_009_margin0⟩

theorem regime008_point005_dominance : WallProjectionCheck 3 ownedP006 ownedP005 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP005]

theorem regime008_point006_dominance : WallProjectionCheck 3 ownedP006 ownedP006 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP006]

theorem regime008_point007_dominance : WallProjectionCheck 3 ownedP006 ownedP007 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP007]

theorem regime008_point008_dominance : WallProjectionCheck 3 ownedP006 ownedP008 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, ownedP008]

theorem regime008_mirror14_005_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_005 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_005]

theorem regime008_mirror14_006_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_006 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_006]

theorem regime008_mirror14_008_dominance : WallProjectionCheck 3 ownedP006 mirrorP14_008 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP006, mirrorP14_008]

theorem regime008_mirror14_009_dominance : WallProjectionCheck 3 mirrorP14_009 mirrorP14_009 (0) (3/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP14_009, mirrorP14_009]

theorem regime008_checked : regime008.Check 1 3 points (0) (3/4) := by
  unfold regime008 AnchoredWallDirectionCertificate.Check
  refine ⟨facet002_mem, facet010_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime008_point006
    · exact regime008_mirror14_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP006, by simp, regime008_point005_dominance⟩
    · exact ⟨ownedP006, by simp, regime008_point006_dominance⟩
    · exact ⟨ownedP006, by simp, regime008_point007_dominance⟩
    · exact ⟨ownedP006, by simp, regime008_point008_dominance⟩
    · exact ⟨ownedP006, by simp, regime008_mirror14_005_dominance⟩
    · exact ⟨ownedP006, by simp, regime008_mirror14_006_dominance⟩
    · exact ⟨ownedP006, by simp, regime008_mirror14_008_dominance⟩
    · exact ⟨mirrorP14_009, by simp, regime008_mirror14_009_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
