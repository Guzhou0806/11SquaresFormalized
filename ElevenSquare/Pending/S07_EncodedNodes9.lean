import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes8
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected72_206 : ¬ Sat compatible supports (childDomains compatible supports domains72 targets72 14 206) (childTargets supports targets72 206) :=
  transport_child domains72 targets72 14 206 domains71 targets71 (by decide) (by decide) rejected71
theorem rejected72 : ¬ Sat compatible supports domains72 targets72 :=
  refute_split compatible supports domains72 targets72 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected72_206, List.forall_mem_nil _⟩)
#print axioms rejected72
set_option maxRecDepth 8192 in
theorem child_rejected73_5 : ¬ Sat compatible supports (childDomains compatible supports domains73 targets73 0 5) (childTargets supports targets73 5) :=
  transport_child domains73 targets73 0 5 domains70 targets70 (by decide) (by decide) rejected70
set_option maxRecDepth 8192 in
theorem child_rejected73_8 : ¬ Sat compatible supports (childDomains compatible supports domains73 targets73 0 8) (childTargets supports targets73 8) :=
  transport_child domains73 targets73 0 8 domains72 targets72 (by decide) (by decide) rejected72
theorem rejected73 : ¬ Sat compatible supports domains73 targets73 :=
  refute_split compatible supports domains73 targets73 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected73_5, (List.forall_mem_cons.mpr ⟨child_rejected73_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected73
theorem rejected74 : ¬ Sat compatible supports domains74 targets74 :=
  refute_empty_domain compatible supports domains74 targets74 2 (by decide)
#print axioms rejected74
set_option maxRecDepth 8192 in
theorem child_rejected75_2 : ¬ Sat compatible supports (childDomains compatible supports domains75 targets75 0 2) (childTargets supports targets75 2) :=
  transport_child domains75 targets75 0 2 domains74 targets74 (by decide) (by decide) rejected74
theorem rejected75 : ¬ Sat compatible supports domains75 targets75 :=
  refute_split compatible supports domains75 targets75 0 [2] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected75_2, List.forall_mem_nil _⟩)
#print axioms rejected75
theorem rejected76 : ¬ Sat compatible supports domains76 targets76 :=
  refute_empty_domain compatible supports domains76 targets76 2 (by decide)
#print axioms rejected76
theorem rejected77 : ¬ Sat compatible supports domains77 targets77 :=
  refute_empty_domain compatible supports domains77 targets77 4 (by decide)
#print axioms rejected77
theorem rejected78 : ¬ Sat compatible supports domains78 targets78 :=
  refute_empty_domain compatible supports domains78 targets78 4 (by decide)
#print axioms rejected78
set_option maxRecDepth 8192 in
theorem child_rejected79_5 : ¬ Sat compatible supports (childDomains compatible supports domains79 targets79 0 5) (childTargets supports targets79 5) :=
  transport_child domains79 targets79 0 5 domains77 targets77 (by decide) (by decide) rejected77
set_option maxRecDepth 8192 in
theorem child_rejected79_8 : ¬ Sat compatible supports (childDomains compatible supports domains79 targets79 0 8) (childTargets supports targets79 8) :=
  transport_child domains79 targets79 0 8 domains78 targets78 (by decide) (by decide) rejected78
theorem rejected79 : ¬ Sat compatible supports domains79 targets79 :=
  refute_split compatible supports domains79 targets79 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected79_5, (List.forall_mem_cons.mpr ⟨child_rejected79_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected79
end ElevenSquare.Pending.EncodedSearch
