import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedNodes50
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem initial_eq2 : initialDomains 2 = domains405 := by decide
set_option maxRecDepth 8192 in
theorem targets_eq2 : List.range 216 = targets405 := by decide
theorem root_rejected2 : ¬ Sat compatible supports (initialDomains 2) (List.range 216) := by
  rw [initial_eq2, targets_eq2]
  exact rejected405
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.root_rejected2
