import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime013 : AnchoredWallDirectionCertificate := .ordinary facet008 facet013 [mirrorP11_012]

theorem regime013_guard : facet008.determinant facet013 ≠ 0 ∧
    (wallDualFirstPolynomial facet008 facet013 3).quartic.BernsteinNonnegCheck (1/8) (1/4) ∧
    (wallDualSecondPolynomial facet008 facet013 3).quartic.BernsteinNonnegCheck (1/8) (1/4) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013]

theorem regime013_mirror11_012_margin0 : (wallDualMargin facet008 facet013 3 mirrorP11_012).BernsteinPosCheck (1/8) (1/4) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet008, facet013, mirrorP11_012]

theorem regime013_mirror11_012 : WallDualCheck facet008 facet013 3 mirrorP11_012 (1/8) (1/4) := by
  rcases regime013_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime013_mirror11_012_margin0⟩

theorem regime013_point005_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP005 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP005]

theorem regime013_point006_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP006]

theorem regime013_point007_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP007]

theorem regime013_point008_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP008]

theorem regime013_point010_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP010]

theorem regime013_point011_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP011]

theorem regime013_point012_dominance : WallProjectionCheck 3 mirrorP11_012 ownedP012 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, ownedP012]

theorem regime013_mirror11_006_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_006 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_006]

theorem regime013_mirror11_007_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_007 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_007]

theorem regime013_mirror11_008_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_008 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_008]

theorem regime013_mirror11_009_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_009 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_009]

theorem regime013_mirror11_010_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_010 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_010]

theorem regime013_mirror11_011_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_011 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_011]

theorem regime013_mirror11_012_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_012 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_012]

theorem regime013_mirror11_013_dominance : WallProjectionCheck 3 mirrorP11_012 mirrorP11_013 (1/8) (1/4) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_013]

theorem regime013_checked : regime013.Check 4 3 points (1/8) (1/4) := by
  unfold regime013 AnchoredWallDirectionCertificate.Check
  refine ⟨facet008_mem, facet013_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    · exact regime013_mirror11_012
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mirrorP11_012, by simp, regime013_point005_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_point006_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_point007_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_point008_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_point010_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_point011_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_point012_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_006_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_007_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_008_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_009_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_010_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_011_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_012_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime013_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
