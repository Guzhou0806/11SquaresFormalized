import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicGuardedCover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def guard : SymbolicQuadratic := ⟨90500000/6812438839, -178307000000/47687071873, -90500000/6812438839⟩
def negativeGuard : SymbolicQuadratic := ⟨-90500000/6812438839, 178307000000/47687071873, 90500000/6812438839⟩
def positiveWitness : GuardedFarkasWitness :=
  ⟨witness02, .plain, .factor ⟨1,0,0⟩, .plain⟩
def negativeWitness : GuardedFarkasWitness :=
  ⟨⟨0, 12, ⟨1, 0, 1⟩, ⟨-1267/178307, 2, 1267/178307⟩, ⟨1000000/534921, 0, -1000000/534921⟩⟩, .factor ⟨47687071873/89153500000, 0, 0⟩, .plain, .plain⟩

theorem positiveWitness_checked :
    positiveWitness.Check source facet02 guard left right := by
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
    baselineRationalCap, left, right, positiveWitness, witness02, facet02, guard]

theorem negativeWitness_checked :
    negativeWitness.Check source facet02 negativeGuard left right := by
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
    baselineRationalCap, left, right, negativeWitness, facet02, negativeGuard]

theorem negativeGuard_eval (t : ℝ) : negativeGuard.eval t = -guard.eval t := by
  dsimp [negativeGuard, guard, SymbolicQuadratic.eval]
  ring

theorem facet02_contains (t : ℝ) (hlt : (left : ℝ) ≤ t)
    (htu : t ≤ (right : ℝ)) (x : Point)
    (hx : SymbolicPolygonContains source t x) : facet02.contains t x := by
  by_cases h : 0 ≤ guard.eval t
  · exact guarded_farkas_sound positiveWitness source facet02 guard left right
      positiveWitness_checked t hlt htu h x hx
  · apply guarded_farkas_sound negativeWitness source facet02 negativeGuard left right
      negativeWitness_checked t hlt htu ?_ x hx
    rw [negativeGuard_eval]
    linarith

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.facet02_contains
