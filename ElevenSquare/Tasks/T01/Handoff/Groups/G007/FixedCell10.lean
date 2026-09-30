import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedAssembly
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window001.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window001.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window004.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window006.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window006.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window007.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window007.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window009.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window009.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window010.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window010.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window011.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window011.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window013.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window013.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window014.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window014.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window015.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window015.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window016.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window016.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window017.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window017.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window018.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window019.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window019.Domain

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending
noncomputable section

theorem fixedCell10_windows :
    ∀ w ∈ fixedCell10Windows, WindowCapture 10 w := by
  intro w hw P hc owners hs t ht0 ht1 ha hl hu
  have hcell := hs.1 10 (by decide : (10 : Fin 16) ∈ support)
  simp only [fixedCell10Windows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply FixedCell10Window000.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window000.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window000.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window001.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window001.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window001.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window002.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window002.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window002.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window003.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window003.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window003.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window004.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window004.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window004.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window005.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window005.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window005.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window006.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window006.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window006.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window007.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window007.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window007.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window008.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window008.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window008.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window009.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window009.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window009.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window010.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window010.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window010.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window011.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window011.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window011.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window012.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window012.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window012.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window013.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window013.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window013.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window014.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window014.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window014.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window015.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window015.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window015.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window016.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window016.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window016.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window017.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window017.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window017.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window018.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window018.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window018.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩
  · apply FixedCell10Window019.capture_from_packing P hc (owners 10) owners
    · exact FixedCell10Window019.row_contains _ hcell (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell10Window019.blockerIndices,
          item.1 ∈ support ∧ (10 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      exact ⟨hs.2 10 (by decide) item.1 hmem hne, hs.1 item.1 hmem⟩

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.fixedCell10_windows
