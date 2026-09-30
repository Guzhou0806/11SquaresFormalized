import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes9
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected80_217 : ¬ Sat compatible supports (childDomains compatible supports domains80 targets80 15 217) (childTargets supports targets80 217) :=
  transport_child domains80 targets80 15 217 domains79 targets79 (by decide) (by decide) rejected79
theorem rejected80 : ¬ Sat compatible supports domains80 targets80 :=
  refute_split compatible supports domains80 targets80 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected80_217, List.forall_mem_nil _⟩)
#print axioms rejected80
set_option maxRecDepth 8192 in
theorem child_rejected81_202 : ¬ Sat compatible supports (childDomains compatible supports domains81 targets81 14 202) (childTargets supports targets81 202) :=
  transport_child domains81 targets81 14 202 domains75 targets75 (by decide) (by decide) rejected75
set_option maxRecDepth 8192 in
theorem child_rejected81_205 : ¬ Sat compatible supports (childDomains compatible supports domains81 targets81 14 205) (childTargets supports targets81 205) :=
  transport_child domains81 targets81 14 205 domains76 targets76 (by decide) (by decide) rejected76
set_option maxRecDepth 8192 in
theorem child_rejected81_206 : ¬ Sat compatible supports (childDomains compatible supports domains81 targets81 14 206) (childTargets supports targets81 206) :=
  transport_child domains81 targets81 14 206 domains80 targets80 (by decide) (by decide) rejected80
theorem rejected81 : ¬ Sat compatible supports domains81 targets81 :=
  refute_split compatible supports domains81 targets81 14 [202, 205, 206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected81_202, (List.forall_mem_cons.mpr ⟨child_rejected81_205, (List.forall_mem_cons.mpr ⟨child_rejected81_206, List.forall_mem_nil _⟩)⟩)⟩)
#print axioms rejected81
theorem rejected82 : ¬ Sat compatible supports domains82 targets82 :=
  refute_empty_domain compatible supports domains82 targets82 4 (by decide)
#print axioms rejected82
set_option maxRecDepth 8192 in
theorem child_rejected83_8 : ¬ Sat compatible supports (childDomains compatible supports domains83 targets83 0 8) (childTargets supports targets83 8) :=
  transport_child domains83 targets83 0 8 domains82 targets82 (by decide) (by decide) rejected82
theorem rejected83 : ¬ Sat compatible supports domains83 targets83 :=
  refute_split compatible supports domains83 targets83 0 [8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected83_8, List.forall_mem_nil _⟩)
#print axioms rejected83
set_option maxRecDepth 8192 in
theorem child_rejected84_21 : ¬ Sat compatible supports (childDomains compatible supports domains84 targets84 2 21) (childTargets supports targets84 21) :=
  transport_child domains84 targets84 2 21 domains83 targets83 (by decide) (by decide) rejected83
theorem rejected84 : ¬ Sat compatible supports domains84 targets84 :=
  refute_split compatible supports domains84 targets84 2 [21] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected84_21, List.forall_mem_nil _⟩)
#print axioms rejected84
theorem rejected85 : ¬ Sat compatible supports domains85 targets85 :=
  refute_empty_domain compatible supports domains85 targets85 4 (by decide)
#print axioms rejected85
theorem rejected86 : ¬ Sat compatible supports domains86 targets86 :=
  refute_empty_domain compatible supports domains86 targets86 10 (by decide)
#print axioms rejected86
set_option maxRecDepth 8192 in
theorem child_rejected87_206 : ¬ Sat compatible supports (childDomains compatible supports domains87 targets87 14 206) (childTargets supports targets87 206) :=
  transport_child domains87 targets87 14 206 domains86 targets86 (by decide) (by decide) rejected86
theorem rejected87 : ¬ Sat compatible supports domains87 targets87 :=
  refute_split compatible supports domains87 targets87 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected87_206, List.forall_mem_nil _⟩)
#print axioms rejected87
end ElevenSquare.Pending.EncodedSearch
