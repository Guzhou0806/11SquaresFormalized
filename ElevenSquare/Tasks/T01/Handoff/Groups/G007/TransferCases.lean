import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask198
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask822
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask835
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask887
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask938
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask940
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask942
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask1217
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask1523
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask1533
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask1540
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2034
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2039
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2060
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2080
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2081
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2141
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2150
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2153
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2155
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Mask2157
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Transfer

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare Pending

/-- Match every archived literal support mask to the frozen public case index. -/
theorem official_mask_rows :
    ∀ entry ∈ rosterMasks,
      ∀ h : entry.1 < 2184, caseMask ⟨entry.1, h⟩ = entry.2 := by
  intro entry he h
  simp only [rosterMasks, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using case_mask_198
  · simpa using case_mask_822
  · simpa using case_mask_835
  · simpa using case_mask_887
  · simpa using case_mask_938
  · simpa using case_mask_940
  · simpa using case_mask_942
  · simpa using case_mask_1217
  · simpa using case_mask_1523
  · simpa using case_mask_1533
  · simpa using case_mask_1540
  · simpa using case_mask_2034
  · simpa using case_mask_2039
  · simpa using case_mask_2060
  · simpa using case_mask_2080
  · simpa using case_mask_2081
  · simpa using case_mask_2141
  · simpa using case_mask_2150
  · simpa using case_mask_2153
  · simpa using case_mask_2155
  · simpa using case_mask_2157

/-- Exact public-case transfer shape. The analytic half-turn of an entire
    packing, when required, is a separate geometry argument. -/
theorem public_support (k : Fin 2184)
    (hk : k.val ∈ groupCases (⟨7, by decide⟩ : Group)) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have hm : k.val ∈ rosterMasks.map Prod.fst := by
    rw [roster_indices]
    exact hk
  obtain ⟨entry, he, hval⟩ := List.mem_map.mp hm
  have hlt : entry.1 < 2184 := by
    rw [hval]
    exact k.isLt
  have hkey : (⟨entry.1, hlt⟩ : Fin 2184) = k := by
    apply Fin.ext
    exact hval
  have hcase : caseMask k = entry.2 := by
    simpa only [hkey] using official_mask_rows entry he hlt
  simpa only [hcase] using literal_support entry he

end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.public_support
