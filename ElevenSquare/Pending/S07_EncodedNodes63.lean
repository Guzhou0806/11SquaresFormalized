import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected504 : ¬ Sat compatible supports domains504 targets504 :=
  refute_empty_domain compatible supports domains504 targets504 8 (by decide)
#print axioms rejected504
theorem rejected505 : ¬ Sat compatible supports domains505 targets505 :=
  refute_empty_domain compatible supports domains505 targets505 2 (by decide)
#print axioms rejected505
theorem rejected506 : ¬ Sat compatible supports domains506 targets506 :=
  refute_empty_domain compatible supports domains506 targets506 2 (by decide)
#print axioms rejected506
theorem rejected507 : ¬ Sat compatible supports domains507 targets507 :=
  refute_empty_domain compatible supports domains507 targets507 9 (by decide)
#print axioms rejected507
theorem rejected508 : ¬ Sat compatible supports domains508 targets508 :=
  refute_empty_domain compatible supports domains508 targets508 10 (by decide)
#print axioms rejected508
theorem rejected509 : ¬ Sat compatible supports domains509 targets509 :=
  refute_empty_domain compatible supports domains509 targets509 11 (by decide)
#print axioms rejected509
set_option maxRecDepth 8192 in
theorem child_rejected510_211 : ¬ Sat compatible supports (childDomains compatible supports domains510 targets510 15 211) (childTargets supports targets510 211) :=
  transport_child domains510 targets510 15 211 domains509 targets509 (by decide) (by decide) rejected509
theorem rejected510 : ¬ Sat compatible supports domains510 targets510 :=
  refute_split compatible supports domains510 targets510 15 [211] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected510_211, List.forall_mem_nil _⟩)
#print axioms rejected510
set_option maxRecDepth 8192 in
theorem child_rejected511_149 : ¬ Sat compatible supports (childDomains compatible supports domains511 targets511 10 149) (childTargets supports targets511 149) :=
  transport_child domains511 targets511 10 149 domains510 targets510 (by decide) (by decide) rejected510
theorem rejected511 : ¬ Sat compatible supports domains511 targets511 :=
  refute_split compatible supports domains511 targets511 10 [149] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected511_149, List.forall_mem_nil _⟩)
#print axioms rejected511
end ElevenSquare.Pending.EncodedSearch
