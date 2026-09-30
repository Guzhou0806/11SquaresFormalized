import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes56
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected456 : ¬ Sat compatible supports domains456 targets456 :=
  refute_empty_domain compatible supports domains456 targets456 2 (by decide)
#print axioms rejected456
set_option maxRecDepth 8192 in
theorem child_rejected457_184 : ¬ Sat compatible supports (childDomains compatible supports domains457 targets457 12 184) (childTargets supports targets457 184) :=
  transport_child domains457 targets457 12 184 domains456 targets456 (by decide) (by decide) rejected456
theorem rejected457 : ¬ Sat compatible supports domains457 targets457 :=
  refute_split compatible supports domains457 targets457 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected457_184, List.forall_mem_nil _⟩)
#print axioms rejected457
theorem rejected458 : ¬ Sat compatible supports domains458 targets458 :=
  refute_empty_domain compatible supports domains458 targets458 10 (by decide)
#print axioms rejected458
theorem rejected459 : ¬ Sat compatible supports domains459 targets459 :=
  refute_empty_domain compatible supports domains459 targets459 10 (by decide)
#print axioms rejected459
set_option maxRecDepth 8192 in
theorem child_rejected460_216 : ¬ Sat compatible supports (childDomains compatible supports domains460 targets460 15 216) (childTargets supports targets460 216) :=
  transport_child domains460 targets460 15 216 domains455 targets455 (by decide) (by decide) rejected455
set_option maxRecDepth 8192 in
theorem child_rejected460_217 : ¬ Sat compatible supports (childDomains compatible supports domains460 targets460 15 217) (childTargets supports targets460 217) :=
  transport_child domains460 targets460 15 217 domains457 targets457 (by decide) (by decide) rejected457
set_option maxRecDepth 8192 in
theorem child_rejected460_218 : ¬ Sat compatible supports (childDomains compatible supports domains460 targets460 15 218) (childTargets supports targets460 218) :=
  transport_child domains460 targets460 15 218 domains458 targets458 (by decide) (by decide) rejected458
set_option maxRecDepth 8192 in
theorem child_rejected460_219 : ¬ Sat compatible supports (childDomains compatible supports domains460 targets460 15 219) (childTargets supports targets460 219) :=
  transport_child domains460 targets460 15 219 domains459 targets459 (by decide) (by decide) rejected459
theorem rejected460 : ¬ Sat compatible supports domains460 targets460 :=
  refute_split compatible supports domains460 targets460 15 [216, 217, 218, 219] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected460_216, (List.forall_mem_cons.mpr ⟨child_rejected460_217, (List.forall_mem_cons.mpr ⟨child_rejected460_218, (List.forall_mem_cons.mpr ⟨child_rejected460_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected460
theorem rejected461 : ¬ Sat compatible supports domains461 targets461 :=
  refute_empty_domain compatible supports domains461 targets461 14 (by decide)
#print axioms rejected461
theorem rejected462 : ¬ Sat compatible supports domains462 targets462 :=
  refute_empty_domain compatible supports domains462 targets462 2 (by decide)
#print axioms rejected462
set_option maxRecDepth 8192 in
theorem child_rejected463_184 : ¬ Sat compatible supports (childDomains compatible supports domains463 targets463 12 184) (childTargets supports targets463 184) :=
  transport_child domains463 targets463 12 184 domains462 targets462 (by decide) (by decide) rejected462
theorem rejected463 : ¬ Sat compatible supports domains463 targets463 :=
  refute_split compatible supports domains463 targets463 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected463_184, List.forall_mem_nil _⟩)
#print axioms rejected463
end ElevenSquare.Pending.EncodedSearch
