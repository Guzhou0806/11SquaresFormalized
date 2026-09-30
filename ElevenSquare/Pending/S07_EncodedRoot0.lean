import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedNodes13
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem initial_eq0 : initialDomains 0 = domains108 := by decide
set_option maxRecDepth 8192 in
theorem targets_eq0 : List.range 216 = targets108 := by decide
theorem root_rejected0 : ¬ Sat compatible supports (initialDomains 0) (List.range 216) := by
  rw [initial_eq0, targets_eq0]
  exact rejected108
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.root_rejected0
