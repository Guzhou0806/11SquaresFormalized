import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet00
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet01
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet02
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet03
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet04
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet05
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet06
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet07
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet08
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet09
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet10
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet11
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet12
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Facet13

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem implication_checked :
    SymbolicPolygonImplicationCheck source target witnesses left right := by
  simp [SymbolicPolygonImplicationCheck, target, witnesses,
    witness00_checked, witness01_checked, witness02_checked, witness03_checked, witness04_checked, witness05_checked, witness06_checked, witness07_checked, witness08_checked, witness09_checked, witness10_checked, witness11_checked, witness12_checked, witness13_checked]

theorem source_implies_target (t : ℝ) (hlt : (left : ℝ) ≤ t)
    (htu : t ≤ (right : ℝ)) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    SymbolicPolygonContains target t x :=
  symbolic_polygon_implication_sound source target witnesses left right
    implication_checked t hlt htu x hx

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.source_implies_target
