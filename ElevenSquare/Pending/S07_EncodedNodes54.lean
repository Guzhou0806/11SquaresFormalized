import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes51
import ElevenSquare.Pending.S07_EncodedNodes52
import ElevenSquare.Pending.S07_EncodedNodes53
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected432_82 : ¬ Sat compatible supports (childDomains compatible supports domains432 targets432 6 82) (childTargets supports targets432 82) :=
  transport_child domains432 targets432 6 82 domains431 targets431 (by decide) (by decide) rejected431
theorem rejected432 : ¬ Sat compatible supports domains432 targets432 :=
  refute_split compatible supports domains432 targets432 6 [82] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected432_82, List.forall_mem_nil _⟩)
#print axioms rejected432
set_option maxRecDepth 8192 in
theorem child_rejected433_170 : ¬ Sat compatible supports (childDomains compatible supports domains433 targets433 11 170) (childTargets supports targets433 170) :=
  transport_child domains433 targets433 11 170 domains432 targets432 (by decide) (by decide) rejected432
theorem rejected433 : ¬ Sat compatible supports domains433 targets433 :=
  refute_split compatible supports domains433 targets433 11 [170] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected433_170, List.forall_mem_nil _⟩)
#print axioms rejected433
set_option maxRecDepth 8192 in
theorem child_rejected434_22 : ¬ Sat compatible supports (childDomains compatible supports domains434 targets434 2 22) (childTargets supports targets434 22) :=
  transport_child domains434 targets434 2 22 domains425 targets425 (by decide) (by decide) rejected425
set_option maxRecDepth 8192 in
theorem child_rejected434_23 : ¬ Sat compatible supports (childDomains compatible supports domains434 targets434 2 23) (childTargets supports targets434 23) :=
  transport_child domains434 targets434 2 23 domains426 targets426 (by decide) (by decide) rejected426
set_option maxRecDepth 8192 in
theorem child_rejected434_25 : ¬ Sat compatible supports (childDomains compatible supports domains434 targets434 2 25) (childTargets supports targets434 25) :=
  transport_child domains434 targets434 2 25 domains433 targets433 (by decide) (by decide) rejected433
theorem rejected434 : ¬ Sat compatible supports domains434 targets434 :=
  refute_split compatible supports domains434 targets434 2 [22, 23, 25] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected434_22, (List.forall_mem_cons.mpr ⟨child_rejected434_23, (List.forall_mem_cons.mpr ⟨child_rejected434_25, List.forall_mem_nil _⟩)⟩)⟩)
#print axioms rejected434
set_option maxRecDepth 8192 in
theorem child_rejected435_101 : ¬ Sat compatible supports (childDomains compatible supports domains435 targets435 7 101) (childTargets supports targets435 101) :=
  transport_child domains435 targets435 7 101 domains415 targets415 (by decide) (by decide) rejected415
set_option maxRecDepth 8192 in
theorem child_rejected435_103 : ¬ Sat compatible supports (childDomains compatible supports domains435 targets435 7 103) (childTargets supports targets435 103) :=
  transport_child domains435 targets435 7 103 domains418 targets418 (by decide) (by decide) rejected418
set_option maxRecDepth 8192 in
theorem child_rejected435_104 : ¬ Sat compatible supports (childDomains compatible supports domains435 targets435 7 104) (childTargets supports targets435 104) :=
  transport_child domains435 targets435 7 104 domains419 targets419 (by decide) (by decide) rejected419
set_option maxRecDepth 8192 in
theorem child_rejected435_108 : ¬ Sat compatible supports (childDomains compatible supports domains435 targets435 7 108) (childTargets supports targets435 108) :=
  transport_child domains435 targets435 7 108 domains434 targets434 (by decide) (by decide) rejected434
theorem rejected435 : ¬ Sat compatible supports domains435 targets435 :=
  refute_split compatible supports domains435 targets435 7 [101, 103, 104, 108] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected435_101, (List.forall_mem_cons.mpr ⟨child_rejected435_103, (List.forall_mem_cons.mpr ⟨child_rejected435_104, (List.forall_mem_cons.mpr ⟨child_rejected435_108, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected435
theorem rejected436 : ¬ Sat compatible supports domains436 targets436 :=
  refute_empty_domain compatible supports domains436 targets436 2 (by decide)
#print axioms rejected436
theorem rejected437 : ¬ Sat compatible supports domains437 targets437 :=
  refute_empty_domain compatible supports domains437 targets437 4 (by decide)
#print axioms rejected437
set_option maxRecDepth 8192 in
theorem child_rejected438_8 : ¬ Sat compatible supports (childDomains compatible supports domains438 targets438 0 8) (childTargets supports targets438 8) :=
  transport_child domains438 targets438 0 8 domains437 targets437 (by decide) (by decide) rejected437
theorem rejected438 : ¬ Sat compatible supports domains438 targets438 :=
  refute_split compatible supports domains438 targets438 0 [8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected438_8, List.forall_mem_nil _⟩)
#print axioms rejected438
theorem rejected439 : ¬ Sat compatible supports domains439 targets439 :=
  refute_empty_domain compatible supports domains439 targets439 5 (by decide)
#print axioms rejected439
end ElevenSquare.Pending.EncodedSearch
