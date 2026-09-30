import ElevenSquare.Tasks.T01.Handoff.Groups.G003.HybridAssembly
import ElevenSquare.Tasks.T01.Field03Cell04Row000.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.Cached.Capture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001.Cached.Capture
import ElevenSquare.Tasks.T01.Field03Cell04Row025.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Cached.Capture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached.Capture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime004.Cached.Capture
import ElevenSquare.Tasks.T01.Field03Cell04Row061.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Cached.Capture
import ElevenSquare.Tasks.T01.Field03Cell04Row066.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached.Capture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007.Cached.Capture
import ElevenSquare.Tasks.T01.Field03Cell04Row071.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Cached.Capture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime009.Cached.Capture
import ElevenSquare.Tasks.T01.Field03Cell04Row075.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached.Capture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime011.Cached.Capture
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.Cached.Capture
import ElevenSquare.Tasks.T01.Field03Cell04Row084.PackingCapture

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached
open ElevenSquare.Pending
noncomputable section

theorem cell04_windows :
    ∀ w ∈ field03Cell04HybridWindows, WindowCapture 1 w := by
  intro w hw P hc owners hinj hcell t ht0 ht1 ha hl hu
  have hc0 : ClosedCell 0
      (normalizeCenter (P.squares (owners 0)).center) := hcell 0
  have hc1 : ClosedCell 4
      (normalizeCenter (P.squares (owners 1)).center) := hcell 1
  have h10 : owners 1 ≠ owners 0 := by
    intro he; exact (by decide : (1 : Fin 4) ≠ 0) (hinj he)
  simp only [field03Cell04HybridWindows, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Field03Cell04Row000.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell04Regime000.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03SymbolicCell04Regime001.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03Cell04Row025.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell04Regime002.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03SymbolicCell04Regime003.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03SymbolicCell04Regime004.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03Cell04Row061.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell04Regime005.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03Cell04Row066.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell04Regime006.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03SymbolicCell04Regime007.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03Cell04Row071.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell04Regime008.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03SymbolicCell04Regime009.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03Cell04Row075.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell04Regime010.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03SymbolicCell04Regime011.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03SymbolicCell04Regime012.Cached.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ha hl hu
  · exact Field03Cell04Row084.capture_from_packing P (owners 1) (owners 0) h10 hc1 hc0 (hc (owners 0))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached.cell04_windows
