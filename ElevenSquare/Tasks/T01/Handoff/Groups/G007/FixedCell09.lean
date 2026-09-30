import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedAssembly
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window000.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window002.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window004.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window006.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window006.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window008.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window009.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window009.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window010.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window010.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window011.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window011.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window012.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window013.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window013.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window014.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window014.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window017.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window019.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window019.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window022.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window022.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window024.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window024.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window025.Domain

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending
noncomputable section

theorem fixedCell09_windows :
    ∀ w ∈ fixedCell09Windows, WindowCapture 9 w := by
  intro w hw P hc owners hs t ht0 ht1 ha hl hu
  have hcell := hs.1 9 (by decide : (9 : Fin 16) ∈ support)
  simp only [fixedCell09Windows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply FixedCell09Window000.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window000.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window000.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window001.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window001.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window001.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window002.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window002.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window002.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window003.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window003.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window003.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window004.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window004.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window004.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window005.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window005.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window005.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window006.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window006.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window006.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window007.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window007.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window007.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window008.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window008.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window008.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window009.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window009.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window009.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window010.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window010.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window010.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window011.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window011.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window011.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window012.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window012.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window012.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window013.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window013.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window013.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window014.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window014.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window014.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window015.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window015.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window015.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window016.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window016.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window016.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window017.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window017.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window017.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window018.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window018.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window018.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window019.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window019.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window019.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window020.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window020.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window020.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window021.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window021.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window021.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window022.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window022.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window022.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window023.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window023.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window023.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window024.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window024.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window024.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell09Window025.capture_from_packing P hc (owners 9) owners
    · exact FixedCell09Window025.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell09Window025.blockerIndices,
          item.1 ∈ support ∧ (9 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 9 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.fixedCell09_windows
