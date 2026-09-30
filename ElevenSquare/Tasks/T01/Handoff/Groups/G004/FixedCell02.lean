import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedAssembly
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window000.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window000.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window001.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window001.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window002.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window002.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window003.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window003.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window004.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window004.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window006.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window006.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window007.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window007.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window008.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window008.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window009.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window009.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window010.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window010.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window011.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window011.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window012.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window012.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window013.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window013.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window014.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window015.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window016.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window018.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window018.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window019.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window019.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window020.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window020.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window021.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window021.Domain
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022.CheckedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window022.Domain

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004
open ElevenSquare.Pending
noncomputable section

theorem fixedCell02_windows :
    ∀ w ∈ fixedCell02Windows, WindowCapture 2 w := by
  intro w hw P hc owners hinj hcell t ht0 ht1 ha hl hu
  have hc2 : ClosedCell 2
      (normalizeCenter (P.squares (owners 2)).center) := hcell 2
  simp only [fixedCell02Windows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply FixedCell02Window000.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window000.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window000.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window001.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window001.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window001.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window002.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window002.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window002.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window003.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window003.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window003.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window004.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window004.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window004.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window005.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window005.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window005.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window006.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window006.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window006.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window007.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window007.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window007.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window008.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window008.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window008.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window009.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window009.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window009.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window010.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window010.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window010.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window011.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window011.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window011.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window012.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window012.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window012.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window013.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window013.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window013.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window014.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window014.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window014.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window015.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window015.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window015.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window016.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window016.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window016.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window017.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window017.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window017.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window018.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window018.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window018.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window019.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window019.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window019.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window020.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window020.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window020.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window021.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window021.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window021.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)
  · apply FixedCell02Window022.capture_from_packing P hc (owners 2)
      (fun c => owners (supportRole c))
    · exact FixedCell02Window022.row_contains _ hc2 (P.contained _) t ht0 ht1 ha
        (by norm_num at hl ⊢ <;> exact hl) (by norm_num at hu ⊢ <;> exact hu)
    · intro item hi
      have hdata : ∀ item ∈ FixedCell02Window022.blockerIndices,
          item.1 ∈ support ∧ (2 : Fin 16) ≠ item.1 := by decide
      obtain ⟨hmem, hne⟩ := hdata item hi
      constructor
      · exact fun he => supportRole_ne 2 item.1 (by decide) hmem hne (hinj he)
      · simpa only [supportRole_spec item.1 hmem] using hcell (supportRole item.1)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.fixedCell02_windows
