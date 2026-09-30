import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes51
import ElevenSquare.Pending.S07_EncodedNodes54
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected440 : ¬ Sat compatible supports domains440 targets440 :=
  refute_empty_domain compatible supports domains440 targets440 6 (by decide)
#print axioms rejected440
theorem rejected441 : ¬ Sat compatible supports domains441 targets441 :=
  refute_empty_domain compatible supports domains441 targets441 0 (by decide)
#print axioms rejected441
theorem rejected442 : ¬ Sat compatible supports domains442 targets442 :=
  refute_empty_domain compatible supports domains442 targets442 13 (by decide)
#print axioms rejected442
set_option maxRecDepth 8192 in
theorem child_rejected443_25 : ¬ Sat compatible supports (childDomains compatible supports domains443 targets443 2 25) (childTargets supports targets443 25) :=
  transport_child domains443 targets443 2 25 domains438 targets438 (by decide) (by decide) rejected438
set_option maxRecDepth 8192 in
theorem child_rejected443_26 : ¬ Sat compatible supports (childDomains compatible supports domains443 targets443 2 26) (childTargets supports targets443 26) :=
  transport_child domains443 targets443 2 26 domains439 targets439 (by decide) (by decide) rejected439
set_option maxRecDepth 8192 in
theorem child_rejected443_28 : ¬ Sat compatible supports (childDomains compatible supports domains443 targets443 2 28) (childTargets supports targets443 28) :=
  transport_child domains443 targets443 2 28 domains440 targets440 (by decide) (by decide) rejected440
set_option maxRecDepth 8192 in
theorem child_rejected443_30 : ¬ Sat compatible supports (childDomains compatible supports domains443 targets443 2 30) (childTargets supports targets443 30) :=
  transport_child domains443 targets443 2 30 domains441 targets441 (by decide) (by decide) rejected441
set_option maxRecDepth 8192 in
theorem child_rejected443_32 : ¬ Sat compatible supports (childDomains compatible supports domains443 targets443 2 32) (childTargets supports targets443 32) :=
  transport_child domains443 targets443 2 32 domains442 targets442 (by decide) (by decide) rejected442
theorem rejected443 : ¬ Sat compatible supports domains443 targets443 :=
  refute_split compatible supports domains443 targets443 2 [25, 26, 28, 30, 32] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected443_25, (List.forall_mem_cons.mpr ⟨child_rejected443_26, (List.forall_mem_cons.mpr ⟨child_rejected443_28, (List.forall_mem_cons.mpr ⟨child_rejected443_30, (List.forall_mem_cons.mpr ⟨child_rejected443_32, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
#print axioms rejected443
set_option maxRecDepth 8192 in
theorem child_rejected444_184 : ¬ Sat compatible supports (childDomains compatible supports domains444 targets444 12 184) (childTargets supports targets444 184) :=
  transport_child domains444 targets444 12 184 domains443 targets443 (by decide) (by decide) rejected443
theorem rejected444 : ¬ Sat compatible supports domains444 targets444 :=
  refute_split compatible supports domains444 targets444 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected444_184, List.forall_mem_nil _⟩)
#print axioms rejected444
theorem rejected445 : ¬ Sat compatible supports domains445 targets445 :=
  refute_empty_domain compatible supports domains445 targets445 2 (by decide)
#print axioms rejected445
theorem rejected446 : ¬ Sat compatible supports domains446 targets446 :=
  refute_empty_domain compatible supports domains446 targets446 2 (by decide)
#print axioms rejected446
set_option maxRecDepth 8192 in
theorem child_rejected447_34 : ¬ Sat compatible supports (childDomains compatible supports domains447 targets447 3 34) (childTargets supports targets447 34) :=
  transport_child domains447 targets447 3 34 domains413 targets413 (by decide) (by decide) rejected413
set_option maxRecDepth 8192 in
theorem child_rejected447_35 : ¬ Sat compatible supports (childDomains compatible supports domains447 targets447 3 35) (childTargets supports targets447 35) :=
  transport_child domains447 targets447 3 35 domains435 targets435 (by decide) (by decide) rejected435
set_option maxRecDepth 8192 in
theorem child_rejected447_36 : ¬ Sat compatible supports (childDomains compatible supports domains447 targets447 3 36) (childTargets supports targets447 36) :=
  transport_child domains447 targets447 3 36 domains436 targets436 (by decide) (by decide) rejected436
set_option maxRecDepth 8192 in
theorem child_rejected447_37 : ¬ Sat compatible supports (childDomains compatible supports domains447 targets447 3 37) (childTargets supports targets447 37) :=
  transport_child domains447 targets447 3 37 domains444 targets444 (by decide) (by decide) rejected444
set_option maxRecDepth 8192 in
theorem child_rejected447_38 : ¬ Sat compatible supports (childDomains compatible supports domains447 targets447 3 38) (childTargets supports targets447 38) :=
  transport_child domains447 targets447 3 38 domains445 targets445 (by decide) (by decide) rejected445
set_option maxRecDepth 8192 in
theorem child_rejected447_39 : ¬ Sat compatible supports (childDomains compatible supports domains447 targets447 3 39) (childTargets supports targets447 39) :=
  transport_child domains447 targets447 3 39 domains446 targets446 (by decide) (by decide) rejected446
theorem rejected447 : ¬ Sat compatible supports domains447 targets447 :=
  refute_split compatible supports domains447 targets447 3 [34, 35, 36, 37, 38, 39] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected447_34, (List.forall_mem_cons.mpr ⟨child_rejected447_35, (List.forall_mem_cons.mpr ⟨child_rejected447_36, (List.forall_mem_cons.mpr ⟨child_rejected447_37, (List.forall_mem_cons.mpr ⟨child_rejected447_38, (List.forall_mem_cons.mpr ⟨child_rejected447_39, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected447
end ElevenSquare.Pending.EncodedSearch
