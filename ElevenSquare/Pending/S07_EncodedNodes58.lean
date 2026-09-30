import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes57
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected464 : ¬ Sat compatible supports domains464 targets464 :=
  refute_empty_domain compatible supports domains464 targets464 10 (by decide)
#print axioms rejected464
theorem rejected465 : ¬ Sat compatible supports domains465 targets465 :=
  refute_empty_domain compatible supports domains465 targets465 10 (by decide)
#print axioms rejected465
set_option maxRecDepth 8192 in
theorem child_rejected466_216 : ¬ Sat compatible supports (childDomains compatible supports domains466 targets466 15 216) (childTargets supports targets466 216) :=
  transport_child domains466 targets466 15 216 domains461 targets461 (by decide) (by decide) rejected461
set_option maxRecDepth 8192 in
theorem child_rejected466_217 : ¬ Sat compatible supports (childDomains compatible supports domains466 targets466 15 217) (childTargets supports targets466 217) :=
  transport_child domains466 targets466 15 217 domains463 targets463 (by decide) (by decide) rejected463
set_option maxRecDepth 8192 in
theorem child_rejected466_218 : ¬ Sat compatible supports (childDomains compatible supports domains466 targets466 15 218) (childTargets supports targets466 218) :=
  transport_child domains466 targets466 15 218 domains464 targets464 (by decide) (by decide) rejected464
set_option maxRecDepth 8192 in
theorem child_rejected466_219 : ¬ Sat compatible supports (childDomains compatible supports domains466 targets466 15 219) (childTargets supports targets466 219) :=
  transport_child domains466 targets466 15 219 domains465 targets465 (by decide) (by decide) rejected465
theorem rejected466 : ¬ Sat compatible supports domains466 targets466 :=
  refute_split compatible supports domains466 targets466 15 [216, 217, 218, 219] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected466_216, (List.forall_mem_cons.mpr ⟨child_rejected466_217, (List.forall_mem_cons.mpr ⟨child_rejected466_218, (List.forall_mem_cons.mpr ⟨child_rejected466_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected466
theorem rejected467 : ¬ Sat compatible supports domains467 targets467 :=
  refute_empty_domain compatible supports domains467 targets467 14 (by decide)
#print axioms rejected467
theorem rejected468 : ¬ Sat compatible supports domains468 targets468 :=
  refute_empty_domain compatible supports domains468 targets468 2 (by decide)
#print axioms rejected468
set_option maxRecDepth 8192 in
theorem child_rejected469_184 : ¬ Sat compatible supports (childDomains compatible supports domains469 targets469 12 184) (childTargets supports targets469 184) :=
  transport_child domains469 targets469 12 184 domains468 targets468 (by decide) (by decide) rejected468
theorem rejected469 : ¬ Sat compatible supports domains469 targets469 :=
  refute_split compatible supports domains469 targets469 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected469_184, List.forall_mem_nil _⟩)
#print axioms rejected469
set_option maxRecDepth 8192 in
theorem child_rejected470_205 : ¬ Sat compatible supports (childDomains compatible supports domains470 targets470 14 205) (childTargets supports targets470 205) :=
  transport_child domains470 targets470 14 205 domains469 targets469 (by decide) (by decide) rejected469
theorem rejected470 : ¬ Sat compatible supports domains470 targets470 :=
  refute_split compatible supports domains470 targets470 14 [205] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected470_205, List.forall_mem_nil _⟩)
#print axioms rejected470
theorem rejected471 : ¬ Sat compatible supports domains471 targets471 :=
  refute_empty_domain compatible supports domains471 targets471 10 (by decide)
#print axioms rejected471
end ElevenSquare.Pending.EncodedSearch
