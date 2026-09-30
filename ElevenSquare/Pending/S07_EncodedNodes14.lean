import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes13
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected112_2 : ¬ Sat compatible supports (childDomains compatible supports domains112 targets112 0 2) (childTargets supports targets112 2) :=
  transport_child domains112 targets112 0 2 domains110 targets110 (by decide) (by decide) rejected110
set_option maxRecDepth 8192 in
theorem child_rejected112_3 : ¬ Sat compatible supports (childDomains compatible supports domains112 targets112 0 3) (childTargets supports targets112 3) :=
  transport_child domains112 targets112 0 3 domains111 targets111 (by decide) (by decide) rejected111
theorem rejected112 : ¬ Sat compatible supports domains112 targets112 :=
  refute_split compatible supports domains112 targets112 0 [2, 3] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected112_2, (List.forall_mem_cons.mpr ⟨child_rejected112_3, List.forall_mem_nil _⟩)⟩)
#print axioms rejected112
theorem rejected113 : ¬ Sat compatible supports domains113 targets113 :=
  refute_empty_domain compatible supports domains113 targets113 0 (by decide)
#print axioms rejected113
theorem rejected114 : ¬ Sat compatible supports domains114 targets114 :=
  refute_empty_domain compatible supports domains114 targets114 0 (by decide)
#print axioms rejected114
set_option maxRecDepth 8192 in
theorem child_rejected115_111 : ¬ Sat compatible supports (childDomains compatible supports domains115 targets115 8 111) (childTargets supports targets115 111) :=
  transport_child domains115 targets115 8 111 domains109 targets109 (by decide) (by decide) rejected109
set_option maxRecDepth 8192 in
theorem child_rejected115_115 : ¬ Sat compatible supports (childDomains compatible supports domains115 targets115 8 115) (childTargets supports targets115 115) :=
  transport_child domains115 targets115 8 115 domains112 targets112 (by decide) (by decide) rejected112
set_option maxRecDepth 8192 in
theorem child_rejected115_116 : ¬ Sat compatible supports (childDomains compatible supports domains115 targets115 8 116) (childTargets supports targets115 116) :=
  transport_child domains115 targets115 8 116 domains113 targets113 (by decide) (by decide) rejected113
set_option maxRecDepth 8192 in
theorem child_rejected115_118 : ¬ Sat compatible supports (childDomains compatible supports domains115 targets115 8 118) (childTargets supports targets115 118) :=
  transport_child domains115 targets115 8 118 domains114 targets114 (by decide) (by decide) rejected114
theorem rejected115 : ¬ Sat compatible supports domains115 targets115 :=
  refute_split compatible supports domains115 targets115 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected115_111, (List.forall_mem_cons.mpr ⟨child_rejected115_115, (List.forall_mem_cons.mpr ⟨child_rejected115_116, (List.forall_mem_cons.mpr ⟨child_rejected115_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected115
set_option maxRecDepth 8192 in
theorem child_rejected116_184 : ¬ Sat compatible supports (childDomains compatible supports domains116 targets116 12 184) (childTargets supports targets116 184) :=
  transport_child domains116 targets116 12 184 domains115 targets115 (by decide) (by decide) rejected115
theorem rejected116 : ¬ Sat compatible supports domains116 targets116 :=
  refute_split compatible supports domains116 targets116 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected116_184, List.forall_mem_nil _⟩)
#print axioms rejected116
theorem rejected117 : ¬ Sat compatible supports domains117 targets117 :=
  refute_empty_domain compatible supports domains117 targets117 8 (by decide)
#print axioms rejected117
theorem rejected118 : ¬ Sat compatible supports domains118 targets118 :=
  refute_empty_domain compatible supports domains118 targets118 8 (by decide)
#print axioms rejected118
theorem rejected119 : ¬ Sat compatible supports domains119 targets119 :=
  refute_empty_domain compatible supports domains119 targets119 14 (by decide)
#print axioms rejected119
end ElevenSquare.Pending.EncodedSearch
