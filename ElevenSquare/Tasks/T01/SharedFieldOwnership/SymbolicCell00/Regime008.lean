import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime008 : AnchoredWallDirectionCertificate := .ordinary facet000 facet012 [ownedP005, mirrorP15_009]

theorem regime008_guard : facet000.determinant facet012 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet012 2).quartic.BernsteinNonnegCheck (1/4) (1) ∧
    (wallDualSecondPolynomial facet000 facet012 2).quartic.BernsteinNonnegCheck (1/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet012]

theorem regime008_point005_margin0 : (wallDualMargin facet000 facet012 2 ownedP005).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet012, ownedP005]

theorem regime008_point005 : WallDualCheck facet000 facet012 2 ownedP005 (1/4) (1) := by
  rcases regime008_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime008_point005_margin0⟩

theorem regime008_mirror15_009_margin0 : (wallDualMargin facet000 facet012 2 mirrorP15_009).BernsteinPosCheck (1/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet012, mirrorP15_009]

theorem regime008_mirror15_009 : WallDualCheck facet000 facet012 2 mirrorP15_009 (1/4) (1) := by
  rcases regime008_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime008_mirror15_009_margin0⟩

theorem regime008_point005_dominance : WallProjectionCheck 2 ownedP005 ownedP005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP005]

theorem regime008_point006_dominance : WallProjectionCheck 2 ownedP005 ownedP006 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP006]

theorem regime008_point007_dominance : WallProjectionCheck 2 ownedP005 ownedP007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP007]

theorem regime008_point009_dominance : WallProjectionCheck 2 ownedP005 ownedP009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP009]

theorem regime008_point010_dominance : WallProjectionCheck 2 ownedP005 ownedP010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, ownedP010]

theorem regime008_mirror15_005_dominance : WallProjectionCheck 2 ownedP005 mirrorP15_005 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP15_005]

theorem regime008_mirror15_007_dominance : WallProjectionCheck 2 ownedP005 mirrorP15_007 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP15_007]

theorem regime008_mirror15_008_dominance : WallProjectionCheck 2 ownedP005 mirrorP15_008 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP005, mirrorP15_008]

theorem regime008_mirror15_009_dominance : WallProjectionCheck 2 mirrorP15_009 mirrorP15_009 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_009, mirrorP15_009]

theorem regime008_mirror15_010_dominance : WallProjectionCheck 2 mirrorP15_009 mirrorP15_010 (1/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP15_009, mirrorP15_010]

theorem regime008_checked : regime008.Check 0 2 points (1/4) (1) := by
  unfold regime008 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet012_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime008_point005
    · exact regime008_mirror15_009
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP005, by simp, regime008_point005_dominance⟩
    · exact ⟨ownedP005, by simp, regime008_point006_dominance⟩
    · exact ⟨ownedP005, by simp, regime008_point007_dominance⟩
    · exact ⟨ownedP005, by simp, regime008_point009_dominance⟩
    · exact ⟨ownedP005, by simp, regime008_point010_dominance⟩
    · exact ⟨ownedP005, by simp, regime008_mirror15_005_dominance⟩
    · exact ⟨ownedP005, by simp, regime008_mirror15_007_dominance⟩
    · exact ⟨ownedP005, by simp, regime008_mirror15_008_dominance⟩
    · exact ⟨mirrorP15_009, by simp, regime008_mirror15_009_dominance⟩
    · exact ⟨mirrorP15_009, by simp, regime008_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
