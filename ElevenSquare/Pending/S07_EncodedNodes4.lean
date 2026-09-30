import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes2
import ElevenSquare.Pending.S07_EncodedNodes3
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected32_200 : ¬ Sat compatible supports (childDomains compatible supports domains32 targets32 14 200) (childTargets supports targets32 200) :=
  transport_child domains32 targets32 14 200 domains20 targets20 (by decide) (by decide) rejected20
set_option maxRecDepth 8192 in
theorem child_rejected32_201 : ¬ Sat compatible supports (childDomains compatible supports domains32 targets32 14 201) (childTargets supports targets32 201) :=
  transport_child domains32 targets32 14 201 domains23 targets23 (by decide) (by decide) rejected23
set_option maxRecDepth 8192 in
theorem child_rejected32_202 : ¬ Sat compatible supports (childDomains compatible supports domains32 targets32 14 202) (childTargets supports targets32 202) :=
  transport_child domains32 targets32 14 202 domains26 targets26 (by decide) (by decide) rejected26
set_option maxRecDepth 8192 in
theorem child_rejected32_203 : ¬ Sat compatible supports (childDomains compatible supports domains32 targets32 14 203) (childTargets supports targets32 203) :=
  transport_child domains32 targets32 14 203 domains28 targets28 (by decide) (by decide) rejected28
set_option maxRecDepth 8192 in
theorem child_rejected32_204 : ¬ Sat compatible supports (childDomains compatible supports domains32 targets32 14 204) (childTargets supports targets32 204) :=
  transport_child domains32 targets32 14 204 domains31 targets31 (by decide) (by decide) rejected31
theorem rejected32 : ¬ Sat compatible supports domains32 targets32 :=
  refute_split compatible supports domains32 targets32 14 [200, 201, 202, 203, 204] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected32_200, (List.forall_mem_cons.mpr ⟨child_rejected32_201, (List.forall_mem_cons.mpr ⟨child_rejected32_202, (List.forall_mem_cons.mpr ⟨child_rejected32_203, (List.forall_mem_cons.mpr ⟨child_rejected32_204, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
#print axioms rejected32
theorem rejected33 : ¬ Sat compatible supports domains33 targets33 :=
  refute_empty_domain compatible supports domains33 targets33 7 (by decide)
#print axioms rejected33
set_option maxRecDepth 8192 in
theorem child_rejected34_29 : ¬ Sat compatible supports (childDomains compatible supports domains34 targets34 2 29) (childTargets supports targets34 29) :=
  transport_child domains34 targets34 2 29 domains33 targets33 (by decide) (by decide) rejected33
theorem rejected34 : ¬ Sat compatible supports domains34 targets34 :=
  refute_split compatible supports domains34 targets34 2 [29] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected34_29, List.forall_mem_nil _⟩)
#print axioms rejected34
theorem rejected35 : ¬ Sat compatible supports domains35 targets35 :=
  refute_empty_domain compatible supports domains35 targets35 15 (by decide)
#print axioms rejected35
set_option maxRecDepth 8192 in
theorem child_rejected36_13 : ¬ Sat compatible supports (childDomains compatible supports domains36 targets36 1 13) (childTargets supports targets36 13) :=
  transport_child domains36 targets36 1 13 domains34 targets34 (by decide) (by decide) rejected34
set_option maxRecDepth 8192 in
theorem child_rejected36_17 : ¬ Sat compatible supports (childDomains compatible supports domains36 targets36 1 17) (childTargets supports targets36 17) :=
  transport_child domains36 targets36 1 17 domains35 targets35 (by decide) (by decide) rejected35
theorem rejected36 : ¬ Sat compatible supports domains36 targets36 :=
  refute_split compatible supports domains36 targets36 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected36_13, (List.forall_mem_cons.mpr ⟨child_rejected36_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected36
theorem rejected37 : ¬ Sat compatible supports domains37 targets37 :=
  refute_empty_domain compatible supports domains37 targets37 6 (by decide)
#print axioms rejected37
set_option maxRecDepth 8192 in
theorem child_rejected38_28 : ¬ Sat compatible supports (childDomains compatible supports domains38 targets38 2 28) (childTargets supports targets38 28) :=
  transport_child domains38 targets38 2 28 domains37 targets37 (by decide) (by decide) rejected37
theorem rejected38 : ¬ Sat compatible supports domains38 targets38 :=
  refute_split compatible supports domains38 targets38 2 [28] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected38_28, List.forall_mem_nil _⟩)
#print axioms rejected38
theorem rejected39 : ¬ Sat compatible supports domains39 targets39 :=
  refute_empty_domain compatible supports domains39 targets39 15 (by decide)
#print axioms rejected39
end ElevenSquare.Pending.EncodedSearch
