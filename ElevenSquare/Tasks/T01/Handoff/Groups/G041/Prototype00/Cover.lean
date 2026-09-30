import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.Leaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.Leaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.Leaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.Leaf006
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem source_eq : source = symbolicWallScaledSlab (4 : Fin 16) := by
  exact ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.source_eq

theorem cover_checked : node000.Check source targets 0 (1/512) := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

theorem wall_cover_checked : node000.Check (symbolicWallScaledSlab (4 : Fin 16)) targets 0 (1/512) := by
  rw [← source_eq]
  exact cover_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.wall_cover_checked
