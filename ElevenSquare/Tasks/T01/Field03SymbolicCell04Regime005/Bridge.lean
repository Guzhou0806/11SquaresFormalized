import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Cover
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem source_eq : source = symbolicWallScaledSlab (4 : Fin 16) := by
  rfl

theorem wall_cover_checked : node000.Check
    (symbolicWallScaledSlab (4 : Fin 16)) targets (647/2048) (897/2048) := by
  rw [← source_eq]
  exact cover_checked

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.wall_cover_checked
