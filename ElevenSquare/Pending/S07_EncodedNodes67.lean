import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes62
import ElevenSquare.Pending.S07_EncodedNodes66
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected536 : ¬ Sat compatible supports domains536 targets536 :=
  refute_empty_domain compatible supports domains536 targets536 4 (by decide)
#print axioms rejected536
set_option maxRecDepth 8192 in
theorem child_rejected537_111 : ¬ Sat compatible supports (childDomains compatible supports domains537 targets537 8 111) (childTargets supports targets537 111) :=
  transport_child domains537 targets537 8 111 domains533 targets533 (by decide) (by decide) rejected533
set_option maxRecDepth 8192 in
theorem child_rejected537_115 : ¬ Sat compatible supports (childDomains compatible supports domains537 targets537 8 115) (childTargets supports targets537 115) :=
  transport_child domains537 targets537 8 115 domains534 targets534 (by decide) (by decide) rejected534
set_option maxRecDepth 8192 in
theorem child_rejected537_116 : ¬ Sat compatible supports (childDomains compatible supports domains537 targets537 8 116) (childTargets supports targets537 116) :=
  transport_child domains537 targets537 8 116 domains535 targets535 (by decide) (by decide) rejected535
set_option maxRecDepth 8192 in
theorem child_rejected537_118 : ¬ Sat compatible supports (childDomains compatible supports domains537 targets537 8 118) (childTargets supports targets537 118) :=
  transport_child domains537 targets537 8 118 domains536 targets536 (by decide) (by decide) rejected536
theorem rejected537 : ¬ Sat compatible supports domains537 targets537 :=
  refute_split compatible supports domains537 targets537 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected537_111, (List.forall_mem_cons.mpr ⟨child_rejected537_115, (List.forall_mem_cons.mpr ⟨child_rejected537_116, (List.forall_mem_cons.mpr ⟨child_rejected537_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected537
set_option maxRecDepth 8192 in
theorem child_rejected538_184 : ¬ Sat compatible supports (childDomains compatible supports domains538 targets538 12 184) (childTargets supports targets538 184) :=
  transport_child domains538 targets538 12 184 domains537 targets537 (by decide) (by decide) rejected537
theorem rejected538 : ¬ Sat compatible supports domains538 targets538 :=
  refute_split compatible supports domains538 targets538 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected538_184, List.forall_mem_nil _⟩)
#print axioms rejected538
theorem rejected539 : ¬ Sat compatible supports domains539 targets539 :=
  refute_empty_domain compatible supports domains539 targets539 2 (by decide)
#print axioms rejected539
theorem rejected540 : ¬ Sat compatible supports domains540 targets540 :=
  refute_empty_domain compatible supports domains540 targets540 2 (by decide)
#print axioms rejected540
set_option maxRecDepth 8192 in
theorem child_rejected541_34 : ¬ Sat compatible supports (childDomains compatible supports domains541 targets541 3 34) (childTargets supports targets541 34) :=
  transport_child domains541 targets541 3 34 domains502 targets502 (by decide) (by decide) rejected502
set_option maxRecDepth 8192 in
theorem child_rejected541_35 : ¬ Sat compatible supports (childDomains compatible supports domains541 targets541 3 35) (childTargets supports targets541 35) :=
  transport_child domains541 targets541 3 35 domains531 targets531 (by decide) (by decide) rejected531
set_option maxRecDepth 8192 in
theorem child_rejected541_36 : ¬ Sat compatible supports (childDomains compatible supports domains541 targets541 3 36) (childTargets supports targets541 36) :=
  transport_child domains541 targets541 3 36 domains532 targets532 (by decide) (by decide) rejected532
set_option maxRecDepth 8192 in
theorem child_rejected541_37 : ¬ Sat compatible supports (childDomains compatible supports domains541 targets541 3 37) (childTargets supports targets541 37) :=
  transport_child domains541 targets541 3 37 domains538 targets538 (by decide) (by decide) rejected538
set_option maxRecDepth 8192 in
theorem child_rejected541_38 : ¬ Sat compatible supports (childDomains compatible supports domains541 targets541 3 38) (childTargets supports targets541 38) :=
  transport_child domains541 targets541 3 38 domains539 targets539 (by decide) (by decide) rejected539
set_option maxRecDepth 8192 in
theorem child_rejected541_39 : ¬ Sat compatible supports (childDomains compatible supports domains541 targets541 3 39) (childTargets supports targets541 39) :=
  transport_child domains541 targets541 3 39 domains540 targets540 (by decide) (by decide) rejected540
theorem rejected541 : ¬ Sat compatible supports domains541 targets541 :=
  refute_split compatible supports domains541 targets541 3 [34, 35, 36, 37, 38, 39] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected541_34, (List.forall_mem_cons.mpr ⟨child_rejected541_35, (List.forall_mem_cons.mpr ⟨child_rejected541_36, (List.forall_mem_cons.mpr ⟨child_rejected541_37, (List.forall_mem_cons.mpr ⟨child_rejected541_38, (List.forall_mem_cons.mpr ⟨child_rejected541_39, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected541
end ElevenSquare.Pending.EncodedSearch
