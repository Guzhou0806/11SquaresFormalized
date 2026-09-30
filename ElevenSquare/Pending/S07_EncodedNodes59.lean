import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes57
import ElevenSquare.Pending.S07_EncodedNodes58
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected472 : ¬ Sat compatible supports domains472 targets472 :=
  refute_empty_domain compatible supports domains472 targets472 10 (by decide)
#print axioms rejected472
set_option maxRecDepth 8192 in
theorem child_rejected473_216 : ¬ Sat compatible supports (childDomains compatible supports domains473 targets473 15 216) (childTargets supports targets473 216) :=
  transport_child domains473 targets473 15 216 domains467 targets467 (by decide) (by decide) rejected467
set_option maxRecDepth 8192 in
theorem child_rejected473_217 : ¬ Sat compatible supports (childDomains compatible supports domains473 targets473 15 217) (childTargets supports targets473 217) :=
  transport_child domains473 targets473 15 217 domains470 targets470 (by decide) (by decide) rejected470
set_option maxRecDepth 8192 in
theorem child_rejected473_218 : ¬ Sat compatible supports (childDomains compatible supports domains473 targets473 15 218) (childTargets supports targets473 218) :=
  transport_child domains473 targets473 15 218 domains471 targets471 (by decide) (by decide) rejected471
set_option maxRecDepth 8192 in
theorem child_rejected473_219 : ¬ Sat compatible supports (childDomains compatible supports domains473 targets473 15 219) (childTargets supports targets473 219) :=
  transport_child domains473 targets473 15 219 domains472 targets472 (by decide) (by decide) rejected472
theorem rejected473 : ¬ Sat compatible supports domains473 targets473 :=
  refute_split compatible supports domains473 targets473 15 [216, 217, 218, 219] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected473_216, (List.forall_mem_cons.mpr ⟨child_rejected473_217, (List.forall_mem_cons.mpr ⟨child_rejected473_218, (List.forall_mem_cons.mpr ⟨child_rejected473_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected473
theorem rejected474 : ¬ Sat compatible supports domains474 targets474 :=
  refute_empty_domain compatible supports domains474 targets474 1 (by decide)
#print axioms rejected474
theorem rejected475 : ¬ Sat compatible supports domains475 targets475 :=
  refute_empty_domain compatible supports domains475 targets475 1 (by decide)
#print axioms rejected475
theorem rejected476 : ¬ Sat compatible supports domains476 targets476 :=
  refute_empty_domain compatible supports domains476 targets476 1 (by decide)
#print axioms rejected476
set_option maxRecDepth 8192 in
theorem child_rejected477_22 : ¬ Sat compatible supports (childDomains compatible supports domains477 targets477 2 22) (childTargets supports targets477 22) :=
  transport_child domains477 targets477 2 22 domains474 targets474 (by decide) (by decide) rejected474
set_option maxRecDepth 8192 in
theorem child_rejected477_23 : ¬ Sat compatible supports (childDomains compatible supports domains477 targets477 2 23) (childTargets supports targets477 23) :=
  transport_child domains477 targets477 2 23 domains475 targets475 (by decide) (by decide) rejected475
set_option maxRecDepth 8192 in
theorem child_rejected477_25 : ¬ Sat compatible supports (childDomains compatible supports domains477 targets477 2 25) (childTargets supports targets477 25) :=
  transport_child domains477 targets477 2 25 domains476 targets476 (by decide) (by decide) rejected476
theorem rejected477 : ¬ Sat compatible supports domains477 targets477 :=
  refute_split compatible supports domains477 targets477 2 [22, 23, 25] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected477_22, (List.forall_mem_cons.mpr ⟨child_rejected477_23, (List.forall_mem_cons.mpr ⟨child_rejected477_25, List.forall_mem_nil _⟩)⟩)⟩)
#print axioms rejected477
set_option maxRecDepth 8192 in
theorem child_rejected478_101 : ¬ Sat compatible supports (childDomains compatible supports domains478 targets478 7 101) (childTargets supports targets478 101) :=
  transport_child domains478 targets478 7 101 domains460 targets460 (by decide) (by decide) rejected460
set_option maxRecDepth 8192 in
theorem child_rejected478_103 : ¬ Sat compatible supports (childDomains compatible supports domains478 targets478 7 103) (childTargets supports targets478 103) :=
  transport_child domains478 targets478 7 103 domains466 targets466 (by decide) (by decide) rejected466
set_option maxRecDepth 8192 in
theorem child_rejected478_104 : ¬ Sat compatible supports (childDomains compatible supports domains478 targets478 7 104) (childTargets supports targets478 104) :=
  transport_child domains478 targets478 7 104 domains473 targets473 (by decide) (by decide) rejected473
set_option maxRecDepth 8192 in
theorem child_rejected478_108 : ¬ Sat compatible supports (childDomains compatible supports domains478 targets478 7 108) (childTargets supports targets478 108) :=
  transport_child domains478 targets478 7 108 domains477 targets477 (by decide) (by decide) rejected477
theorem rejected478 : ¬ Sat compatible supports domains478 targets478 :=
  refute_split compatible supports domains478 targets478 7 [101, 103, 104, 108] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected478_101, (List.forall_mem_cons.mpr ⟨child_rejected478_103, (List.forall_mem_cons.mpr ⟨child_rejected478_104, (List.forall_mem_cons.mpr ⟨child_rejected478_108, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected478
theorem rejected479 : ¬ Sat compatible supports domains479 targets479 :=
  refute_empty_domain compatible supports domains479 targets479 2 (by decide)
#print axioms rejected479
end ElevenSquare.Pending.EncodedSearch
