import ElevenSquare.Orientation
import ElevenSquare.Cases
import ElevenSquare.Pending.S05_Trace

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- An initialized terminal trace excludes an unordered cell mask, with no
orientation assumption left on the input packing. -/
theorem excludes_of_terminal_trace (m : Finset (Fin 16))
    (a b : PoseState)
    (hroot : ∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a)
    (htrace : VerifiedTrace a b) (hterminal : Terminal b) :
    ∀ P : Packing 11 coverCap, ¬ Occupies P m := by
  intro P hocc
  obtain ⟨R, t, ht, hsame⟩ := P.exists_chart
  have hcharted : IsCharted R := by
    intro i
    exact ⟨t i, (ht i).1, (ht i).2.1, (ht i).2.2⟩
  have hoccR : Occupies R m := by
    rcases hocc with ⟨c, hc, hmask, hcell⟩
    refine ⟨c, hc, hmask, ?_⟩
    intro i
    rw [← (hsame i).center_eq]
    exact hcell i
  obtain ⟨perm, hinitial⟩ := hroot R hcharted hoccR
  exact terminal_contradiction (relabelPacking R perm) b
    (verified_trace_sound (relabelPacking R perm) hinitial htrace) hterminal

end
end ElevenSquare.Tasks.T02
