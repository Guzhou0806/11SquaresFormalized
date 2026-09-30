import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes16
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected136 : ¬ Sat compatible supports domains136 targets136 :=
  refute_empty_domain compatible supports domains136 targets136 13 (by decide)
#print axioms rejected136
theorem rejected137 : ¬ Sat compatible supports domains137 targets137 :=
  refute_empty_domain compatible supports domains137 targets137 1 (by decide)
#print axioms rejected137
set_option maxRecDepth 8192 in
theorem child_rejected138_2 : ¬ Sat compatible supports (childDomains compatible supports domains138 targets138 0 2) (childTargets supports targets138 2) :=
  transport_child domains138 targets138 0 2 domains136 targets136 (by decide) (by decide) rejected136
set_option maxRecDepth 8192 in
theorem child_rejected138_3 : ¬ Sat compatible supports (childDomains compatible supports domains138 targets138 0 3) (childTargets supports targets138 3) :=
  transport_child domains138 targets138 0 3 domains137 targets137 (by decide) (by decide) rejected137
theorem rejected138 : ¬ Sat compatible supports domains138 targets138 :=
  refute_split compatible supports domains138 targets138 0 [2, 3] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected138_2, (List.forall_mem_cons.mpr ⟨child_rejected138_3, List.forall_mem_nil _⟩)⟩)
#print axioms rejected138
theorem rejected139 : ¬ Sat compatible supports domains139 targets139 :=
  refute_empty_domain compatible supports domains139 targets139 13 (by decide)
#print axioms rejected139
theorem rejected140 : ¬ Sat compatible supports domains140 targets140 :=
  refute_empty_domain compatible supports domains140 targets140 1 (by decide)
#print axioms rejected140
set_option maxRecDepth 8192 in
theorem child_rejected141_2 : ¬ Sat compatible supports (childDomains compatible supports domains141 targets141 0 2) (childTargets supports targets141 2) :=
  transport_child domains141 targets141 0 2 domains139 targets139 (by decide) (by decide) rejected139
set_option maxRecDepth 8192 in
theorem child_rejected141_3 : ¬ Sat compatible supports (childDomains compatible supports domains141 targets141 0 3) (childTargets supports targets141 3) :=
  transport_child domains141 targets141 0 3 domains140 targets140 (by decide) (by decide) rejected140
theorem rejected141 : ¬ Sat compatible supports domains141 targets141 :=
  refute_split compatible supports domains141 targets141 0 [2, 3] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected141_2, (List.forall_mem_cons.mpr ⟨child_rejected141_3, List.forall_mem_nil _⟩)⟩)
#print axioms rejected141
theorem rejected142 : ¬ Sat compatible supports domains142 targets142 :=
  refute_empty_domain compatible supports domains142 targets142 13 (by decide)
#print axioms rejected142
set_option maxRecDepth 8192 in
theorem child_rejected143_111 : ¬ Sat compatible supports (childDomains compatible supports domains143 targets143 8 111) (childTargets supports targets143 111) :=
  transport_child domains143 targets143 8 111 domains135 targets135 (by decide) (by decide) rejected135
set_option maxRecDepth 8192 in
theorem child_rejected143_115 : ¬ Sat compatible supports (childDomains compatible supports domains143 targets143 8 115) (childTargets supports targets143 115) :=
  transport_child domains143 targets143 8 115 domains138 targets138 (by decide) (by decide) rejected138
set_option maxRecDepth 8192 in
theorem child_rejected143_116 : ¬ Sat compatible supports (childDomains compatible supports domains143 targets143 8 116) (childTargets supports targets143 116) :=
  transport_child domains143 targets143 8 116 domains141 targets141 (by decide) (by decide) rejected141
set_option maxRecDepth 8192 in
theorem child_rejected143_118 : ¬ Sat compatible supports (childDomains compatible supports domains143 targets143 8 118) (childTargets supports targets143 118) :=
  transport_child domains143 targets143 8 118 domains142 targets142 (by decide) (by decide) rejected142
theorem rejected143 : ¬ Sat compatible supports domains143 targets143 :=
  refute_split compatible supports domains143 targets143 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected143_111, (List.forall_mem_cons.mpr ⟨child_rejected143_115, (List.forall_mem_cons.mpr ⟨child_rejected143_116, (List.forall_mem_cons.mpr ⟨child_rejected143_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected143
end ElevenSquare.Pending.EncodedSearch
