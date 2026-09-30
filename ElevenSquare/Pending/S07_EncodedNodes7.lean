import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes6
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected56_28 : ¬ Sat compatible supports (childDomains compatible supports domains56 targets56 2 28) (childTargets supports targets56 28) :=
  transport_child domains56 targets56 2 28 domains54 targets54 (by decide) (by decide) rejected54
set_option maxRecDepth 8192 in
theorem child_rejected56_29 : ¬ Sat compatible supports (childDomains compatible supports domains56 targets56 2 29) (childTargets supports targets56 29) :=
  transport_child domains56 targets56 2 29 domains55 targets55 (by decide) (by decide) rejected55
theorem rejected56 : ¬ Sat compatible supports domains56 targets56 :=
  refute_split compatible supports domains56 targets56 2 [28, 29] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected56_28, (List.forall_mem_cons.mpr ⟨child_rejected56_29, List.forall_mem_nil _⟩)⟩)
#print axioms rejected56
theorem rejected57 : ¬ Sat compatible supports domains57 targets57 :=
  refute_empty_domain compatible supports domains57 targets57 4 (by decide)
#print axioms rejected57
set_option maxRecDepth 8192 in
theorem child_rejected58_5 : ¬ Sat compatible supports (childDomains compatible supports domains58 targets58 0 5) (childTargets supports targets58 5) :=
  transport_child domains58 targets58 0 5 domains57 targets57 (by decide) (by decide) rejected57
theorem rejected58 : ¬ Sat compatible supports domains58 targets58 :=
  refute_split compatible supports domains58 targets58 0 [5] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected58_5, List.forall_mem_nil _⟩)
#print axioms rejected58
theorem rejected59 : ¬ Sat compatible supports domains59 targets59 :=
  refute_empty_domain compatible supports domains59 targets59 0 (by decide)
#print axioms rejected59
theorem rejected60 : ¬ Sat compatible supports domains60 targets60 :=
  refute_empty_domain compatible supports domains60 targets60 0 (by decide)
#print axioms rejected60
theorem rejected61 : ¬ Sat compatible supports domains61 targets61 :=
  refute_empty_domain compatible supports domains61 targets61 0 (by decide)
#print axioms rejected61
theorem rejected62 : ¬ Sat compatible supports domains62 targets62 :=
  refute_empty_domain compatible supports domains62 targets62 0 (by decide)
#print axioms rejected62
set_option maxRecDepth 8192 in
theorem child_rejected63_21 : ¬ Sat compatible supports (childDomains compatible supports domains63 targets63 2 21) (childTargets supports targets63 21) :=
  transport_child domains63 targets63 2 21 domains58 targets58 (by decide) (by decide) rejected58
set_option maxRecDepth 8192 in
theorem child_rejected63_27 : ¬ Sat compatible supports (childDomains compatible supports domains63 targets63 2 27) (childTargets supports targets63 27) :=
  transport_child domains63 targets63 2 27 domains59 targets59 (by decide) (by decide) rejected59
set_option maxRecDepth 8192 in
theorem child_rejected63_28 : ¬ Sat compatible supports (childDomains compatible supports domains63 targets63 2 28) (childTargets supports targets63 28) :=
  transport_child domains63 targets63 2 28 domains60 targets60 (by decide) (by decide) rejected60
set_option maxRecDepth 8192 in
theorem child_rejected63_29 : ¬ Sat compatible supports (childDomains compatible supports domains63 targets63 2 29) (childTargets supports targets63 29) :=
  transport_child domains63 targets63 2 29 domains61 targets61 (by decide) (by decide) rejected61
set_option maxRecDepth 8192 in
theorem child_rejected63_33 : ¬ Sat compatible supports (childDomains compatible supports domains63 targets63 2 33) (childTargets supports targets63 33) :=
  transport_child domains63 targets63 2 33 domains62 targets62 (by decide) (by decide) rejected62
theorem rejected63 : ¬ Sat compatible supports domains63 targets63 :=
  refute_split compatible supports domains63 targets63 2 [21, 27, 28, 29, 33] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected63_21, (List.forall_mem_cons.mpr ⟨child_rejected63_27, (List.forall_mem_cons.mpr ⟨child_rejected63_28, (List.forall_mem_cons.mpr ⟨child_rejected63_29, (List.forall_mem_cons.mpr ⟨child_rejected63_33, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
#print axioms rejected63
end ElevenSquare.Pending.EncodedSearch
