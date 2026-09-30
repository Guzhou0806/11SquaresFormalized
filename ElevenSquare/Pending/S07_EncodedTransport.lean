import ElevenSquare.Pending.S07_EncodedData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation

theorem transport_child (D : Domains) (T : List ℕ) (v r : ℕ)
    (E : Domains) (U : List ℕ)
    (he : childDomains compatible supports D T v r = E)
    (hu : childTargets supports T r = U)
    (h : ¬ Sat compatible supports E U) :
    ¬ Sat compatible supports (childDomains compatible supports D T v r)
      (childTargets supports T r) := by
  rw [he, hu]
  exact h

end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.transport_child
