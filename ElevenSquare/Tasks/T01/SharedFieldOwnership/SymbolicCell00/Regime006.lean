import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime006 : AnchoredWallDirectionCertificate := .ordinary facet000 facet012 [ownedP009, ownedP010]

theorem regime006_guard : facet000.determinant facet012 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet012 2).quartic.BernsteinNonnegCheck (1/8) (3/16) ∧
    (wallDualSecondPolynomial facet000 facet012 2).quartic.BernsteinNonnegCheck (1/8) (3/16) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet012]

theorem regime006_point009_margin0 : (wallDualMargin facet000 facet012 2 ownedP009).BernsteinPosCheck (1/8) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet012, ownedP009]

theorem regime006_point009 : WallDualCheck facet000 facet012 2 ownedP009 (1/8) (3/16) := by
  rcases regime006_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime006_point009_margin0⟩

theorem regime006_point010_margin0 : (wallDualMargin facet000 facet012 2 ownedP010).BernsteinPosCheck (1/8) (3/16) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet012, ownedP010]

theorem regime006_point010 : WallDualCheck facet000 facet012 2 ownedP010 (1/8) (3/16) := by
  rcases regime006_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime006_point010_margin0⟩

theorem regime006_point005_dominance : WallProjectionCheck 2 ownedP009 ownedP005 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP005]

theorem regime006_point006_dominance : WallProjectionCheck 2 ownedP009 ownedP006 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP006]

theorem regime006_point007_dominance : WallProjectionCheck 2 ownedP009 ownedP007 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime006_point009_dominance : WallProjectionCheck 2 ownedP009 ownedP009 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime006_point010_dominance : WallProjectionCheck 2 ownedP010 ownedP010 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, ownedP010]

theorem regime006_mirror15_005_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_005 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_005]

theorem regime006_mirror15_007_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_007 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_007]

theorem regime006_mirror15_008_dominance : WallProjectionCheck 2 ownedP010 mirrorP15_008 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP010, mirrorP15_008]

theorem regime006_mirror15_009_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_009 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_009]

theorem regime006_mirror15_010_dominance : WallProjectionCheck 2 ownedP009 mirrorP15_010 (1/8) (3/16) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_010]

theorem regime006_checked : regime006.Check 0 2 points (1/8) (3/16) := by
  unfold regime006 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet012_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime006_point009
    · exact regime006_point010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP009, by simp, regime006_point005_dominance⟩
    · exact ⟨ownedP009, by simp, regime006_point006_dominance⟩
    · exact ⟨ownedP009, by simp, regime006_point007_dominance⟩
    · exact ⟨ownedP009, by simp, regime006_point009_dominance⟩
    · exact ⟨ownedP010, by simp, regime006_point010_dominance⟩
    · exact ⟨ownedP009, by simp, regime006_mirror15_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime006_mirror15_007_dominance⟩
    · exact ⟨ownedP010, by simp, regime006_mirror15_008_dominance⟩
    · exact ⟨ownedP009, by simp, regime006_mirror15_009_dominance⟩
    · exact ⟨ownedP009, by simp, regime006_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
