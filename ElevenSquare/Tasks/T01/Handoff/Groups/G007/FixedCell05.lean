import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedAssembly
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window001.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window003.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window003.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window004.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window006.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window006.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window007.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window007.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window009.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window009.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window011.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Domain

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending
noncomputable section

theorem fixedCell05_windows :
    ∀ w ∈ fixedCell05Windows, WindowCapture 5 w := by
  intro w hw P hc owners hs t ht0 ht1 ha hl hu
  have hcell := hs.1 5 (by decide : (5 : Fin 16) ∈ support)
  simp only [fixedCell05Windows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply FixedCell05Window000.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window000.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window000.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window001.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window001.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window001.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window002.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window002.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window002.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window003.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window003.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window003.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window004.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window004.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window004.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window005.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window005.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window005.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window006.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window006.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window006.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window007.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window007.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window007.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window008.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window008.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window008.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window009.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window009.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window009.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window010.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window010.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window010.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window011.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window011.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window011.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window012.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window012.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window012.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell05Window013.capture_from_packing P hc (owners 5) owners
    · exact FixedCell05Window013.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell05Window013.blockerIndices,
          item.1 ∈ support ∧ (5 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 5 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.fixedCell05_windows
