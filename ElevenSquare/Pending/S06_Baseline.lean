import ElevenSquare.Tasks.T01.Handoff.Assembly
import ElevenSquare.Tasks.T01.Exclusion
import ElevenSquare.Orientation
import ElevenSquare.Cases
import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.S05_Trace

/-! UNFINISHED FORMALIZATION OBLIGATIONS. See handoffs/S06_Baseline.md.
Every `sorry` in this file is an explicit outstanding proof, not verified evidence. -/

namespace ElevenSquare.Pending
noncomputable section

def Excluded (k : Fin 2184) : Prop :=
  ∀ P : Packing 11 coverCap, ¬ Occupies P (caseMask k)

-- Build a root, a trace, and a terminal state for EACH actual index.
-- Initial ownership must come from geometry, including all ancestors and angle seams.
theorem baseline_certificate_exists (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  exact ElevenSquare.Tasks.T01.Handoff.all_certificates k hk

theorem baseline_excluded (k : Fin 2184) (hk : k.val ∈ baselineIndices) : Excluded k := by
  obtain ⟨a, b, hroot, htrace, hterminal⟩ := baseline_certificate_exists k hk
  exact ElevenSquare.Tasks.T01.excludes_of_terminal_trace
    (caseMask k) a b hroot htrace hterminal


end
end ElevenSquare.Pending
