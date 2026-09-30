import ElevenSquare.Tasks.T06.BranchDigitData

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem digit_selection_10 :
    ∀ d e f g h : Fin 2, ∀ p : Fin 14,
      rawSelections (digitIndex 1 0 2 d e f g h) p =
        digitChoices 1 0 2 d e f g h p := by
  intro d e f g h p
  fin_cases d <;> fin_cases e <;> fin_cases f <;>
    fin_cases g <;> fin_cases h <;> rfl

end
end ElevenSquare.Tasks.T06
