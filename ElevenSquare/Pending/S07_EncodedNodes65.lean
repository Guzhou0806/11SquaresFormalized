import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes64
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected520_40 : ¬ Sat compatible supports (childDomains compatible supports domains520 targets520 4 40) (childTargets supports targets520 40) :=
  transport_child domains520 targets520 4 40 domains519 targets519 (by decide) (by decide) rejected519
theorem rejected520 : ¬ Sat compatible supports domains520 targets520 :=
  refute_split compatible supports domains520 targets520 4 [40] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected520_40, List.forall_mem_nil _⟩)
#print axioms rejected520
theorem rejected521 : ¬ Sat compatible supports domains521 targets521 :=
  refute_empty_domain compatible supports domains521 targets521 4 (by decide)
#print axioms rejected521
set_option maxRecDepth 8192 in
theorem child_rejected522_111 : ¬ Sat compatible supports (childDomains compatible supports domains522 targets522 8 111) (childTargets supports targets522 111) :=
  transport_child domains522 targets522 8 111 domains515 targets515 (by decide) (by decide) rejected515
set_option maxRecDepth 8192 in
theorem child_rejected522_115 : ¬ Sat compatible supports (childDomains compatible supports domains522 targets522 8 115) (childTargets supports targets522 115) :=
  transport_child domains522 targets522 8 115 domains516 targets516 (by decide) (by decide) rejected516
set_option maxRecDepth 8192 in
theorem child_rejected522_116 : ¬ Sat compatible supports (childDomains compatible supports domains522 targets522 8 116) (childTargets supports targets522 116) :=
  transport_child domains522 targets522 8 116 domains520 targets520 (by decide) (by decide) rejected520
set_option maxRecDepth 8192 in
theorem child_rejected522_118 : ¬ Sat compatible supports (childDomains compatible supports domains522 targets522 8 118) (childTargets supports targets522 118) :=
  transport_child domains522 targets522 8 118 domains521 targets521 (by decide) (by decide) rejected521
theorem rejected522 : ¬ Sat compatible supports domains522 targets522 :=
  refute_split compatible supports domains522 targets522 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected522_111, (List.forall_mem_cons.mpr ⟨child_rejected522_115, (List.forall_mem_cons.mpr ⟨child_rejected522_116, (List.forall_mem_cons.mpr ⟨child_rejected522_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected522
theorem rejected523 : ¬ Sat compatible supports domains523 targets523 :=
  refute_empty_domain compatible supports domains523 targets523 13 (by decide)
#print axioms rejected523
theorem rejected524 : ¬ Sat compatible supports domains524 targets524 :=
  refute_empty_domain compatible supports domains524 targets524 4 (by decide)
#print axioms rejected524
theorem rejected525 : ¬ Sat compatible supports domains525 targets525 :=
  refute_empty_domain compatible supports domains525 targets525 10 (by decide)
#print axioms rejected525
set_option maxRecDepth 8192 in
theorem child_rejected526_138 : ¬ Sat compatible supports (childDomains compatible supports domains526 targets526 9 138) (childTargets supports targets526 138) :=
  transport_child domains526 targets526 9 138 domains525 targets525 (by decide) (by decide) rejected525
theorem rejected526 : ¬ Sat compatible supports domains526 targets526 :=
  refute_split compatible supports domains526 targets526 9 [138] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected526_138, List.forall_mem_nil _⟩)
#print axioms rejected526
set_option maxRecDepth 8192 in
theorem child_rejected527_29 : ¬ Sat compatible supports (childDomains compatible supports domains527 targets527 2 29) (childTargets supports targets527 29) :=
  transport_child domains527 targets527 2 29 domains526 targets526 (by decide) (by decide) rejected526
theorem rejected527 : ¬ Sat compatible supports domains527 targets527 :=
  refute_split compatible supports domains527 targets527 2 [29] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected527_29, List.forall_mem_nil _⟩)
#print axioms rejected527
end ElevenSquare.Pending.EncodedSearch
