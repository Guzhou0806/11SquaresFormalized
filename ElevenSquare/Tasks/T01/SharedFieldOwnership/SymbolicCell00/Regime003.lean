import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime003 : AnchoredWallDirectionCertificate := .ordinary facet012 facet013 [ownedP009]

theorem regime003_guard : facet012.determinant facet013 ≠ 0 ∧
    (wallDualFirstPolynomial facet012 facet013 0).quartic.BernsteinNonnegCheck (5/8) (1) ∧
    (wallDualSecondPolynomial facet012 facet013 0).quartic.BernsteinNonnegCheck (5/8) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet012, facet013]

theorem regime003_point009_margin0 : (wallDualMargin facet012 facet013 0 ownedP009).BernsteinPosCheck (5/8) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet012, facet013, ownedP009]

theorem regime003_point009 : WallDualCheck facet012 facet013 0 ownedP009 (5/8) (1) := by
  rcases regime003_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime003_point009_margin0⟩

theorem regime003_point005_dominance : WallProjectionCheck 0 ownedP009 ownedP005 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP005]

theorem regime003_point006_dominance : WallProjectionCheck 0 ownedP009 ownedP006 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP006]

theorem regime003_point007_dominance : WallProjectionCheck 0 ownedP009 ownedP007 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP007]

theorem regime003_point009_dominance : WallProjectionCheck 0 ownedP009 ownedP009 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP009]

theorem regime003_point010_dominance : WallProjectionCheck 0 ownedP009 ownedP010 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, ownedP010]

theorem regime003_mirror15_005_dominance : WallProjectionCheck 0 ownedP009 mirrorP15_005 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_005]

theorem regime003_mirror15_007_dominance : WallProjectionCheck 0 ownedP009 mirrorP15_007 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_007]

theorem regime003_mirror15_008_dominance : WallProjectionCheck 0 ownedP009 mirrorP15_008 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_008]

theorem regime003_mirror15_009_dominance : WallProjectionCheck 0 ownedP009 mirrorP15_009 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_009]

theorem regime003_mirror15_010_dominance : WallProjectionCheck 0 ownedP009 mirrorP15_010 (5/8) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP009, mirrorP15_010]

theorem regime003_checked : regime003.Check 0 0 points (5/8) (1) := by
  unfold regime003 AnchoredWallDirectionCertificate.Check
  refine ⟨facet012_mem, facet013_mem, ?_, ?_⟩
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
    · exact ⟨ownedP009, by simp, regime003_point009_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_point010_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror15_005_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror15_007_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror15_008_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror15_009_dominance⟩
    · exact ⟨ownedP009, by simp, regime003_mirror15_010_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
