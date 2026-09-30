import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedNodes62
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem initial_eq4 : initialDomains 4 = domains496 := by decide
set_option maxRecDepth 8192 in
theorem targets_eq4 : List.range 216 = targets496 := by decide
theorem root_rejected4 : ¬ Sat compatible supports (initialDomains 4) (List.range 216) := by
  rw [initial_eq4, targets_eq4]
  exact rejected496
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.root_rejected4
