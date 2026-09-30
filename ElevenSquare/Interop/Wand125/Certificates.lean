import ElevenSquare.Interop.Wand125.Cells
import ElevenSquare.Pending.S06_TupleBounds
import ElevenSquare.Pending.S05_Trace
import Sqpack.S11Opt.ImportedFields

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
noncomputable section

def applicable (k : Fin 2184) : Bool :=
  SquarePacking.S11Opt.ImportedFields.applicable recordedCaseTuples[k.val]!

theorem excluded (k : Fin 2184) (hk : applicable k = true)
    (P : Packing 11 coverCap) : ¬ Occupies P (caseMask k) := by
  have hklt : k.val < recordedCaseTuples.size := by
    rw [recorded_case_tuple_bounds.1]
    exact k.isLt
  have hmem : recordedCaseTuples[k.val]! ∈ recordedCaseTuples.toList := by
    simpa [getElem!_pos, hklt] using
      (Array.getElem_mem_toList (xs := recordedCaseTuples) hklt)
  have hJ := (recorded_case_tuple_bounds.2 _ hmem).2
  exact excludes_occupancy _ hJ
    (SquarePacking.S11Opt.ImportedFields.applicable_sound hJ hk) P

/-- Feed the imported geometric contradiction into the existing trace contract,
using the same empty-state construction as the completed native groups. -/
theorem certificate (k : Fin 2184) (hk : applicable k = true) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨emptyState, emptyState, ?_, VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P _ ho
  exact (excluded k hk P ho).elim

end
end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.excluded
#print axioms ElevenSquare.Interop.Wand125.certificate
