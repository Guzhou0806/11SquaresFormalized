import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cover
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem source_eq : source = symbolicWallScaledSlab (8 : Fin 16) := by
  rfl

theorem wall_cover_checked : node000.Check
    (symbolicWallScaledSlab (8 : Fin 16)) targets (633/1024) (1423/2048) := by
  rw [← source_eq]
  exact cover_checked

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.wall_cover_checked
