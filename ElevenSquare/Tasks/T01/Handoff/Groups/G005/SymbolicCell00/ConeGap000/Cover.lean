import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet00
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet01
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet02
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet03
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet04
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet05
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet06
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet07
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet08
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Facet09
namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem source_implies_target (t : ℝ) (hlt : (left : ℝ) ≤ t)
    (htu : t ≤ (right : ℝ)) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    SymbolicPolygonContains target t x := by
  intro f hf
  simp only [target, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact symbolic_farkas_sound witness00 source facet00 left right
      witness00_checked t hlt htu x hx
  · exact symbolic_farkas_sound witness01 source facet01 left right
      witness01_checked t hlt htu x hx
  · exact facet02_contains t hlt htu x hx
  · exact symbolic_farkas_sound witness03 source facet03 left right
      witness03_checked t hlt htu x hx
  · exact symbolic_farkas_sound witness04 source facet04 left right
      witness04_checked t hlt htu x hx
  · exact symbolic_farkas_sound witness05 source facet05 left right
      witness05_checked t hlt htu x hx
  · exact symbolic_farkas_sound witness06 source facet06 left right
      witness06_checked t hlt htu x hx
  · exact symbolic_farkas_sound witness07 source facet07 left right
      witness07_checked t hlt htu x hx
  · exact symbolic_farkas_sound witness08 source facet08 left right
      witness08_checked t hlt htu x hx
  · exact symbolic_farkas_sound witness09 source facet09 left right
      witness09_checked t hlt htu x hx

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.source_implies_target
