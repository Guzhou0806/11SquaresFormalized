import ElevenSquare.Orientation
import ElevenSquare.Cover
import ElevenSquare.Pending.S05_Trace

namespace ElevenSquare.Pending.T03
noncomputable section

/-- A change of square representation preserves the actual occupied cells. -/
theorem occupies_of_sameSquares {S : ℝ} (P R : Packing 11 S)
    (h : ∀ i, SameSquare (P.squares i) (R.squares i))
    (m : Finset (Fin 16)) (hm : Occupies P m) : Occupies R m := by
  rcases hm with ⟨a, ha, himage, hcell⟩
  refine ⟨a, ha, himage, ?_⟩
  intro i
  rw [← (h i).center_eq]
  exact hcell i

/-- Normalize all eleven axes without imposing an extra orientation premise. -/
theorem exists_charted_occupancy {S : ℝ} (P : Packing 11 S)
    (m : Finset (Fin 16)) (hm : Occupies P m) :
    ∃ R : Packing 11 S, IsCharted R ∧ Occupies R m := by
  obtain ⟨R, t, ht, hs⟩ := P.exists_chart
  refine ⟨R, ?_, occupies_of_sameSquares P R hs m hm⟩
  intro i
  exact ⟨t i, (ht i).1, (ht i).2.1, (ht i).2.2⟩

/-- Complete a case exclusion from its initialized terminal trace. -/
theorem exclude_of_certificate (m : Finset (Fin 16))
    (hc : ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b) :
    ∀ P : Packing 11 coverCap, ¬ Occupies P m := by
  intro P hp
  obtain ⟨R, hr, hm⟩ := exists_charted_occupancy P m hp
  obtain ⟨a, b, hinit, htrace, hterminal⟩ := hc
  obtain ⟨perm, hs⟩ := hinit R hr hm
  exact terminal_contradiction (relabelPacking R perm) b
    (verified_trace_sound (relabelPacking R perm) hs htrace) hterminal

end
end ElevenSquare.Pending.T03
