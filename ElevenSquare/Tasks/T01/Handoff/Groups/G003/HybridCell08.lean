import ElevenSquare.Tasks.T01.Handoff.Groups.G003.HybridAssembly
import ElevenSquare.Tasks.T01.Field03Cell08Row000.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.MedianCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime001.MedianCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime002.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row005.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.MedianCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row011.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime006.MedianCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row015.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime008.MedianCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row176.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row303.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row316.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.MedianCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row340.PackingCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.MedianCapture
import ElevenSquare.Tasks.T01.Field03Cell08Row353.PackingCapture

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G003
open ElevenSquare.Pending
noncomputable section

theorem cell08_windows :
    ∀ w ∈ field03Cell08HybridWindows, WindowCapture 2 w := by
  intro w hw P hc owners hinj hcell t ht0 ht1 ha hl hu
  have hc1 : ClosedCell 4
      (normalizeCenter (P.squares (owners 1)).center) := hcell 1
  have hc2 : ClosedCell 8
      (normalizeCenter (P.squares (owners 2)).center) := hcell 2
  have hc3 : ClosedCell 12
      (normalizeCenter (P.squares (owners 3)).center) := hcell 3
  have h21 : owners 2 ≠ owners 1 := by
    intro he; exact (by decide : (2 : Fin 4) ≠ 1) (hinj he)
  have h23 : owners 2 ≠ owners 3 := by
    intro he; exact (by decide : (2 : Fin 4) ≠ 3) (hinj he)
  simp only [field03Cell08HybridWindows, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Field03Cell08Row000.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime000.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03SymbolicCell08Regime001.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03SymbolicCell08Regime002.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row005.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime003.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03SymbolicCell08Regime004.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row011.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime006.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03SymbolicCell08Regime007.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row015.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime008.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03SymbolicCell08Regime009.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row176.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime010.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row303.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime011.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row316.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime012.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03SymbolicCell08Regime013.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row340.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
  · exact Field03SymbolicCell08Regime014.capture_from_packing P (owners 2) (owners 3) h23 hc2 hc3 (hc (owners 3))
      t ha hl hu
  · exact Field03Cell08Row353.capture_from_packing P (owners 2) (owners 1) (owners 3) h21 h23 hc2 hc1 hc3 (hc (owners 3))
      t ht0 ht1 ha (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.cell08_windows
