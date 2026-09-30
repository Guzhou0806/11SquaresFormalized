import ElevenSquare.Interop.Wand125.Coverage.Rows

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem newCases_checked : newCases.all checkedCase = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hlt : k < 2184 := of_decide_eq_true (List.all_eq_true.mp newCases_bound k hk)
  have hm : recordedCaseTuples[k]! ∈ newRows := by
    rw [← newRows_eq]
    exact List.mem_map.mpr ⟨k, hk, rfl⟩
  have h := List.all_eq_true.mp newRows_checked _ hm
  simpa [checkedCase, hlt, applicable] using h

end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.newCases_checked
