import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedNodes67
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem initial_eq5 : initialDomains 5 = domains541 := by decide
set_option maxRecDepth 8192 in
theorem targets_eq5 : List.range 216 = targets541 := by decide
theorem root_rejected5 : ¬ Sat compatible supports (initialDomains 5) (List.range 216) := by
  rw [initial_eq5, targets_eq5]
  exact rejected541
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.root_rejected5
