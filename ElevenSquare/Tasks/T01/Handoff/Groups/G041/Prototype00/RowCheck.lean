import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.BlockerCheck01
import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.BlockerCheck02
import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.BlockerCheck03
import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.BlockerCheck04

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem rowCert_checked : rowCert.Check 4 0 (1/512) := by
  refine ⟨?_, ?_, ?_⟩
  · change source = symbolicWallScaledSlab 4
    exact source_eq
  · change node000.Check source targets 0 (1/512)
    exact cover_checked
  · intro target ht
    simp only [rowCert, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact target01_checked
    · exact target02_checked
    · exact target03_checked
    · exact target04_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.rowCert_checked
