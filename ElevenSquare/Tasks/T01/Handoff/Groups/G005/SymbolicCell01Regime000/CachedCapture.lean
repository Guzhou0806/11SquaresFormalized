import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Semantic
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Cached.Cover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem window_capture : G005.WindowCapture 1 (left, right) := by
  apply window_capture_of_cover
  intro t hlt htu x hx
  exact symbolic_cached_cover_sound Cached.cache Cached.cache_checked
    source targets left right node000 Cached.signNode000
    Cached.cover_checked t hlt htu x hx

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.window_capture
