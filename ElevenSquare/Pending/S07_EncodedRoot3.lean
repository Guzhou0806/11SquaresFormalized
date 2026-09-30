import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedNodes55
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem initial_eq3 : initialDomains 3 = domains447 := by decide
set_option maxRecDepth 8192 in
theorem targets_eq3 : List.range 216 = targets447 := by decide
theorem root_rejected3 : ¬ Sat compatible supports (initialDomains 3) (List.range 216) := by
  rw [initial_eq3, targets_eq3]
  exact rejected447
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.root_rejected3
