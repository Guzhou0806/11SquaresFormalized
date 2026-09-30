import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicGuardedCover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def guard : SymbolicQuadratic := ⟨1, -174831/268211, -1⟩
def negativeGuard : SymbolicQuadratic := ⟨-1, 174831/268211, 1⟩
def positiveWitness : GuardedFarkasWitness :=
  ⟨witness03, .factor ⟨1,0,0⟩, .plain, .plain⟩
def negativeWitness : GuardedFarkasWitness :=
  ⟨⟨9, 13, ⟨1, 0, 1⟩, ⟨532329000000/286195087637, 720058000000/286195087637, -532329000000/286195087637⟩, ⟨-536422000000/286195087637, 349662000000/286195087637, 536422000000/286195087637⟩⟩, .plain, .factor ⟨536422000000/286195087637, 0, 0⟩, .plain⟩

theorem positiveWitness_checked :
    positiveWitness.Check source facet03 guard left right := by
  norm_num [GuardedFarkasWitness.Check, GuardedSignCertificate.Check,
    SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    quarticAdd, quarticSub, List.getD,
    source, symbolicWallScaledSlab, symbolicWallSlab,
    scaledWallFacet, SymbolicQuadratic.scaleByChart,
    SymbolicWallFacet.ofHalfplane, baselineCellPolygon,
    baselineCenterBox, baselineBisector, baselineRationalSite,
    baselineRationalCap, left, right, positiveWitness, witness03, facet03, guard]

theorem negativeWitness_checked :
    negativeWitness.Check source facet03 negativeGuard left right := by
  norm_num [GuardedFarkasWitness.Check, GuardedSignCertificate.Check,
    SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    quarticAdd, quarticSub, List.getD,
    source, symbolicWallScaledSlab, symbolicWallSlab,
    scaledWallFacet, SymbolicQuadratic.scaleByChart,
    SymbolicWallFacet.ofHalfplane, baselineCellPolygon,
    baselineCenterBox, baselineBisector, baselineRationalSite,
    baselineRationalCap, left, right, negativeWitness, facet03, negativeGuard]

theorem negativeGuard_eval (t : ℝ) : negativeGuard.eval t = -guard.eval t := by
  dsimp [negativeGuard, guard, SymbolicQuadratic.eval]
  ring

theorem facet03_contains (t : ℝ) (hlt : (left : ℝ) ≤ t)
    (htu : t ≤ (right : ℝ)) (x : Point)
    (hx : SymbolicPolygonContains source t x) : facet03.contains t x := by
  by_cases h : 0 ≤ guard.eval t
  · exact guarded_farkas_sound positiveWitness source facet03 guard left right
      positiveWitness_checked t hlt htu h x hx
  · apply guarded_farkas_sound negativeWitness source facet03 negativeGuard left right
      negativeWitness_checked t hlt htu ?_ x hx
    rw [negativeGuard_eval]
    linarith

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.facet03_contains
