import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime006 : AnchoredWallDirectionCertificate := .ordinary facet000 facet008 [mirrorP11_010]

theorem regime006_guard : facet000.determinant facet008 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (1/2) (5/8) ∧
    (wallDualSecondPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (1/2) (5/8) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008]

theorem regime006_mirror11_010_margin0 : (wallDualMargin facet000 facet008 1 mirrorP11_010).BernsteinPosCheck (1/2) (5/8) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, mirrorP11_010]

theorem regime006_mirror11_010 : WallDualCheck facet000 facet008 1 mirrorP11_010 (1/2) (5/8) := by
  rcases regime006_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime006_mirror11_010_margin0⟩

theorem regime006_point005_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP005 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP005]

theorem regime006_point006_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP006]

theorem regime006_point007_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP007]

theorem regime006_point008_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP008]

theorem regime006_point010_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP010]

theorem regime006_point011_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP011]

theorem regime006_point012_dominance : WallProjectionCheck 1 mirrorP11_010 ownedP012 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, ownedP012]

theorem regime006_mirror11_006_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_006 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_006]

theorem regime006_mirror11_007_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_007 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_007]

theorem regime006_mirror11_008_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_008 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_008]

theorem regime006_mirror11_009_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_009 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_009]

theorem regime006_mirror11_010_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_010 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_010]

theorem regime006_mirror11_011_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_011 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_011]

theorem regime006_mirror11_012_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_012 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_012]

theorem regime006_mirror11_013_dominance : WallProjectionCheck 1 mirrorP11_010 mirrorP11_013 (1/2) (5/8) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_010, mirrorP11_013]

theorem regime006_checked : regime006.Check 4 1 points (1/2) (5/8) := by
  unfold regime006 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime006_mirror11_010
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP11_010, by simp, regime006_point005_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_point006_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_point007_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_point008_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_point010_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_point011_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_point012_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_006_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_007_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_008_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_009_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_010_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_011_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_012_dominance⟩
    · exact ⟨mirrorP11_010, by simp, regime006_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
