import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected416 : ¬ Sat compatible supports domains416 targets416 :=
  refute_empty_domain compatible supports domains416 targets416 4 (by decide)
#print axioms rejected416
set_option maxRecDepth 8192 in
theorem child_rejected417_8 : ¬ Sat compatible supports (childDomains compatible supports domains417 targets417 0 8) (childTargets supports targets417 8) :=
  transport_child domains417 targets417 0 8 domains416 targets416 (by decide) (by decide) rejected416
theorem rejected417 : ¬ Sat compatible supports domains417 targets417 :=
  refute_split compatible supports domains417 targets417 0 [8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected417_8, List.forall_mem_nil _⟩)
#print axioms rejected417
set_option maxRecDepth 8192 in
theorem child_rejected418_179 : ¬ Sat compatible supports (childDomains compatible supports domains418 targets418 11 179) (childTargets supports targets418 179) :=
  transport_child domains418 targets418 11 179 domains417 targets417 (by decide) (by decide) rejected417
theorem rejected418 : ¬ Sat compatible supports domains418 targets418 :=
  refute_split compatible supports domains418 targets418 11 [179] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected418_179, List.forall_mem_nil _⟩)
#print axioms rejected418
theorem rejected419 : ¬ Sat compatible supports domains419 targets419 :=
  refute_empty_domain compatible supports domains419 targets419 11 (by decide)
#print axioms rejected419
theorem rejected420 : ¬ Sat compatible supports domains420 targets420 :=
  refute_empty_domain compatible supports domains420 targets420 13 (by decide)
#print axioms rejected420
set_option maxRecDepth 8192 in
theorem child_rejected421_183 : ¬ Sat compatible supports (childDomains compatible supports domains421 targets421 12 183) (childTargets supports targets421 183) :=
  transport_child domains421 targets421 12 183 domains420 targets420 (by decide) (by decide) rejected420
theorem rejected421 : ¬ Sat compatible supports domains421 targets421 :=
  refute_split compatible supports domains421 targets421 12 [183] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected421_183, List.forall_mem_nil _⟩)
#print axioms rejected421
set_option maxRecDepth 8192 in
theorem child_rejected422_86 : ¬ Sat compatible supports (childDomains compatible supports domains422 targets422 6 86) (childTargets supports targets422 86) :=
  transport_child domains422 targets422 6 86 domains421 targets421 (by decide) (by decide) rejected421
theorem rejected422 : ¬ Sat compatible supports domains422 targets422 :=
  refute_split compatible supports domains422 targets422 6 [86] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected422_86, List.forall_mem_nil _⟩)
#print axioms rejected422
set_option maxRecDepth 8192 in
theorem child_rejected423_48 : ¬ Sat compatible supports (childDomains compatible supports domains423 targets423 4 48) (childTargets supports targets423 48) :=
  transport_child domains423 targets423 4 48 domains422 targets422 (by decide) (by decide) rejected422
theorem rejected423 : ¬ Sat compatible supports domains423 targets423 :=
  refute_split compatible supports domains423 targets423 4 [48] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected423_48, List.forall_mem_nil _⟩)
#print axioms rejected423
end ElevenSquare.Pending.EncodedSearch
