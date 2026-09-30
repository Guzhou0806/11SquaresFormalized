import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedNodes22
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem initial_eq1 : initialDomains 1 = domains183 := by decide
set_option maxRecDepth 8192 in
theorem targets_eq1 : List.range 216 = targets183 := by decide
theorem root_rejected1 : ¬ Sat compatible supports (initialDomains 1) (List.range 216) := by
  rw [initial_eq1, targets_eq1]
  exact rejected183
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.root_rejected1
