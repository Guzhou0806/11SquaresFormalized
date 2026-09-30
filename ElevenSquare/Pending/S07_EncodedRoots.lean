import ElevenSquare.Pending.S07_EncodedRoot0
import ElevenSquare.Pending.S07_EncodedRoot1
import ElevenSquare.Pending.S07_EncodedRoot2
import ElevenSquare.Pending.S07_EncodedRoot3
import ElevenSquare.Pending.S07_EncodedRoot4
import ElevenSquare.Pending.S07_EncodedRoot5
import Mathlib.Tactic.FinCases
namespace ElevenSquare.Pending.EncodedSearch
open Propagation

theorem all_roots_rejected (k : Fin 6) :
    ¬ Sat compatible supports (initialDomains k.val) (List.range 216) := by
  fin_cases k
  · exact root_rejected0
  · exact root_rejected1
  · exact root_rejected2
  · exact root_rejected3
  · exact root_rejected4
  · exact root_rejected5

end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.all_roots_rejected
