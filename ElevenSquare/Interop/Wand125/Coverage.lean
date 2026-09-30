import ElevenSquare.Interop.Wand125.Coverage.Applicability
import ElevenSquare.Interop.Wand125.Coverage.Inventory

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem new_case_excluded (k : Fin 2184) (hk : k.val ∈ newCases)
    (P : Packing 11 coverCap) : ¬ Occupies P (caseMask k) := by
  have h := List.all_eq_true.mp newCases_checked k.val hk
  have ha : applicable k = true := by simpa [checkedCase, k.isLt] using h
  exact excluded k ha P

end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.newCases_length

#print axioms ElevenSquare.Interop.Wand125.newCases_nodup

#print axioms ElevenSquare.Interop.Wand125.newCases_checked

#print axioms ElevenSquare.Interop.Wand125.newCases_baseline

#print axioms ElevenSquare.Interop.Wand125.newCases_disjoint

#print axioms ElevenSquare.Interop.Wand125.new_case_excluded
