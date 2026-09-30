import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def regime008 : AnchoredWallDirectionCertificate := .ordinary facet000 facet008 [ownedP008, mirrorP11_012]

theorem regime008_guard : facet000.determinant facet008 ≠ 0 ∧
    (wallDualFirstPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (3/4) (1) ∧
    (wallDualSecondPolynomial facet000 facet008 1).quartic.BernsteinNonnegCheck (3/4) (1) := by
  norm_num [WallDualCheck, WallDualCrossingCheck, wallDualFirstPolynomial, wallDualSecondPolynomial, wallDualMargin, WallQuadratic.quartic, WallQuadratic.linear, WallQuadratic.negScale, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008]

theorem regime008_point008_margin0 : (wallDualMargin facet000 facet008 1 ownedP008).BernsteinPosCheck (3/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, ownedP008]

theorem regime008_point008 : WallDualCheck facet000 facet008 1 ownedP008 (3/4) (1) := by
  rcases regime008_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime008_point008_margin0⟩

theorem regime008_mirror11_012_margin0 : (wallDualMargin facet000 facet008 1 mirrorP11_012).BernsteinPosCheck (3/4) (1) := by
  norm_num [wallDualMargin, wallDualFirstPolynomial, wallDualSecondPolynomial, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinPosCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, SymbolicWallFacet.determinant, facet000, facet008, mirrorP11_012]

theorem regime008_mirror11_012 : WallDualCheck facet000 facet008 1 mirrorP11_012 (3/4) (1) := by
  rcases regime008_guard with ⟨hdet, hfirst, hsecond⟩
  exact ⟨hdet, hfirst, hsecond, regime008_mirror11_012_margin0⟩

theorem regime008_point005_dominance : WallProjectionCheck 1 ownedP008 ownedP005 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP005]

theorem regime008_point006_dominance : WallProjectionCheck 1 ownedP008 ownedP006 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP006]

theorem regime008_point007_dominance : WallProjectionCheck 1 ownedP008 ownedP007 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP007]

theorem regime008_point008_dominance : WallProjectionCheck 1 ownedP008 ownedP008 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP008]

theorem regime008_point010_dominance : WallProjectionCheck 1 ownedP008 ownedP010 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP010]

theorem regime008_point011_dominance : WallProjectionCheck 1 ownedP008 ownedP011 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP011]

theorem regime008_point012_dominance : WallProjectionCheck 1 ownedP008 ownedP012 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, ownedP012]

theorem regime008_mirror11_006_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_006 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_006]

theorem regime008_mirror11_007_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_007 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_007]

theorem regime008_mirror11_008_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_008 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_008]

theorem regime008_mirror11_009_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_009 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_009]

theorem regime008_mirror11_010_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_010 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_010]

theorem regime008_mirror11_011_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_011 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_011]

theorem regime008_mirror11_012_dominance : WallProjectionCheck 1 mirrorP11_012 mirrorP11_012 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, mirrorP11_012, mirrorP11_012]

theorem regime008_mirror11_013_dominance : WallProjectionCheck 1 ownedP008 mirrorP11_013 (3/4) (1) := by
  norm_num [WallProjectionCheck, wallProjectionDifference, WallQuadratic.quartic, WallQuadratic.linear, wallDirectionPolynomials, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein, ownedP008, mirrorP11_013]

theorem regime008_checked : regime008.Check 4 1 points (3/4) (1) := by
  unfold regime008 AnchoredWallDirectionCertificate.Check
  refine ⟨facet000_mem, facet008_mem, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact regime008_point008
    · exact regime008_mirror11_012
  · intro p hp
    simp only [points, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ownedP008, by simp, regime008_point005_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point006_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point007_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point008_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point010_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point011_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_point012_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror11_006_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror11_007_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror11_008_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror11_009_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror11_010_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror11_011_dominance⟩
    · exact ⟨mirrorP11_012, by simp, regime008_mirror11_012_dominance⟩
    · exact ⟨ownedP008, by simp, regime008_mirror11_013_dominance⟩

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
