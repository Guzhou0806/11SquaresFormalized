import ElevenSquare.Pending.S07_Assignment
import ElevenSquare.Pending.S07_EncodeAssignment
import ElevenSquare.Pending.S07_EncodedRoots

/-! Finite forbidden-assignment refutation. The original predicate is preserved
in S07_Assignment; the sound search, its data correspondence, and all six raw
source-mask cases are proved by the imported modules. -/
namespace ElevenSquare.Pending
noncomputable section

theorem finite_no_avoiding_assignment : ¬ ∃ f : Owner → Fin 220, AvoidingAssignment f := by
  rintro ⟨f, hf⟩
  obtain ⟨k, hk⟩ := EncodedSearch.avoiding_encoded f hf
  exact EncodedSearch.all_roots_rejected k hk

end
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.finite_no_avoiding_assignment
