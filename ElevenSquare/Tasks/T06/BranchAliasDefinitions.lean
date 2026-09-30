import ElevenSquare.Tasks.T06.BranchInventory

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def RawEnabled (r : Fin 512) : Gap → Prop
  | .wall _ _ _ => True
  | .pair f _ => ∃ p : Fin 14, allFeatures (rawSelections r p) = f

instance rawEnabledDecidable (r : Fin 512) : DecidablePred (RawEnabled r)
  | .wall _ _ _ => inferInstanceAs (Decidable True)
  | .pair f _ => inferInstanceAs
      (Decidable (∃ p : Fin 14, allFeatures (rawSelections r p) = f))

end
end ElevenSquare.Tasks.T06
