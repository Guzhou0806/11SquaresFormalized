import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes52
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected424_68 : ¬ Sat compatible supports (childDomains compatible supports domains424 targets424 5 68) (childTargets supports targets424 68) :=
  transport_child domains424 targets424 5 68 domains423 targets423 (by decide) (by decide) rejected423
theorem rejected424 : ¬ Sat compatible supports domains424 targets424 :=
  refute_split compatible supports domains424 targets424 5 [68] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected424_68, List.forall_mem_nil _⟩)
#print axioms rejected424
set_option maxRecDepth 8192 in
theorem child_rejected425_2 : ¬ Sat compatible supports (childDomains compatible supports domains425 targets425 0 2) (childTargets supports targets425 2) :=
  transport_child domains425 targets425 0 2 domains424 targets424 (by decide) (by decide) rejected424
theorem rejected425 : ¬ Sat compatible supports domains425 targets425 :=
  refute_split compatible supports domains425 targets425 0 [2] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected425_2, List.forall_mem_nil _⟩)
#print axioms rejected425
theorem rejected426 : ¬ Sat compatible supports domains426 targets426 :=
  refute_empty_domain compatible supports domains426 targets426 12 (by decide)
#print axioms rejected426
theorem rejected427 : ¬ Sat compatible supports domains427 targets427 :=
  refute_empty_domain compatible supports domains427 targets427 13 (by decide)
#print axioms rejected427
set_option maxRecDepth 8192 in
theorem child_rejected428_183 : ¬ Sat compatible supports (childDomains compatible supports domains428 targets428 12 183) (childTargets supports targets428 183) :=
  transport_child domains428 targets428 12 183 domains427 targets427 (by decide) (by decide) rejected427
theorem rejected428 : ¬ Sat compatible supports domains428 targets428 :=
  refute_split compatible supports domains428 targets428 12 [183] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected428_183, List.forall_mem_nil _⟩)
#print axioms rejected428
set_option maxRecDepth 8192 in
theorem child_rejected429_48 : ¬ Sat compatible supports (childDomains compatible supports domains429 targets429 4 48) (childTargets supports targets429 48) :=
  transport_child domains429 targets429 4 48 domains428 targets428 (by decide) (by decide) rejected428
theorem rejected429 : ¬ Sat compatible supports domains429 targets429 :=
  refute_split compatible supports domains429 targets429 4 [48] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected429_48, List.forall_mem_nil _⟩)
#print axioms rejected429
set_option maxRecDepth 8192 in
theorem child_rejected430_2 : ¬ Sat compatible supports (childDomains compatible supports domains430 targets430 0 2) (childTargets supports targets430 2) :=
  transport_child domains430 targets430 0 2 domains429 targets429 (by decide) (by decide) rejected429
theorem rejected430 : ¬ Sat compatible supports domains430 targets430 :=
  refute_split compatible supports domains430 targets430 0 [2] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected430_2, List.forall_mem_nil _⟩)
#print axioms rejected430
set_option maxRecDepth 8192 in
theorem child_rejected431_71 : ¬ Sat compatible supports (childDomains compatible supports domains431 targets431 5 71) (childTargets supports targets431 71) :=
  transport_child domains431 targets431 5 71 domains430 targets430 (by decide) (by decide) rejected430
theorem rejected431 : ¬ Sat compatible supports domains431 targets431 :=
  refute_split compatible supports domains431 targets431 5 [71] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected431_71, List.forall_mem_nil _⟩)
#print axioms rejected431
end ElevenSquare.Pending.EncodedSearch
