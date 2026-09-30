import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes62
import ElevenSquare.Pending.S07_EncodedNodes63
import ElevenSquare.Pending.S07_EncodedNodes64
import ElevenSquare.Pending.S07_EncodedNodes65
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected528_40 : ¬ Sat compatible supports (childDomains compatible supports domains528 targets528 4 40) (childTargets supports targets528 40) :=
  transport_child domains528 targets528 4 40 domains527 targets527 (by decide) (by decide) rejected527
theorem rejected528 : ¬ Sat compatible supports domains528 targets528 :=
  refute_split compatible supports domains528 targets528 4 [40] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected528_40, List.forall_mem_nil _⟩)
#print axioms rejected528
theorem rejected529 : ¬ Sat compatible supports domains529 targets529 :=
  refute_empty_domain compatible supports domains529 targets529 4 (by decide)
#print axioms rejected529
set_option maxRecDepth 8192 in
theorem child_rejected530_111 : ¬ Sat compatible supports (childDomains compatible supports domains530 targets530 8 111) (childTargets supports targets530 111) :=
  transport_child domains530 targets530 8 111 domains523 targets523 (by decide) (by decide) rejected523
set_option maxRecDepth 8192 in
theorem child_rejected530_115 : ¬ Sat compatible supports (childDomains compatible supports domains530 targets530 8 115) (childTargets supports targets530 115) :=
  transport_child domains530 targets530 8 115 domains524 targets524 (by decide) (by decide) rejected524
set_option maxRecDepth 8192 in
theorem child_rejected530_116 : ¬ Sat compatible supports (childDomains compatible supports domains530 targets530 8 116) (childTargets supports targets530 116) :=
  transport_child domains530 targets530 8 116 domains528 targets528 (by decide) (by decide) rejected528
set_option maxRecDepth 8192 in
theorem child_rejected530_118 : ¬ Sat compatible supports (childDomains compatible supports domains530 targets530 8 118) (childTargets supports targets530 118) :=
  transport_child domains530 targets530 8 118 domains529 targets529 (by decide) (by decide) rejected529
theorem rejected530 : ¬ Sat compatible supports domains530 targets530 :=
  refute_split compatible supports domains530 targets530 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected530_111, (List.forall_mem_cons.mpr ⟨child_rejected530_115, (List.forall_mem_cons.mpr ⟨child_rejected530_116, (List.forall_mem_cons.mpr ⟨child_rejected530_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected530
set_option maxRecDepth 8192 in
theorem child_rejected531_180 : ¬ Sat compatible supports (childDomains compatible supports domains531 targets531 12 180) (childTargets supports targets531 180) :=
  transport_child domains531 targets531 12 180 domains503 targets503 (by decide) (by decide) rejected503
set_option maxRecDepth 8192 in
theorem child_rejected531_181 : ¬ Sat compatible supports (childDomains compatible supports domains531 targets531 12 181) (childTargets supports targets531 181) :=
  transport_child domains531 targets531 12 181 domains504 targets504 (by decide) (by decide) rejected504
set_option maxRecDepth 8192 in
theorem child_rejected531_182 : ¬ Sat compatible supports (childDomains compatible supports domains531 targets531 12 182) (childTargets supports targets531 182) :=
  transport_child domains531 targets531 12 182 domains513 targets513 (by decide) (by decide) rejected513
set_option maxRecDepth 8192 in
theorem child_rejected531_183 : ¬ Sat compatible supports (childDomains compatible supports domains531 targets531 12 183) (childTargets supports targets531 183) :=
  transport_child domains531 targets531 12 183 domains514 targets514 (by decide) (by decide) rejected514
set_option maxRecDepth 8192 in
theorem child_rejected531_184 : ¬ Sat compatible supports (childDomains compatible supports domains531 targets531 12 184) (childTargets supports targets531 184) :=
  transport_child domains531 targets531 12 184 domains522 targets522 (by decide) (by decide) rejected522
set_option maxRecDepth 8192 in
theorem child_rejected531_185 : ¬ Sat compatible supports (childDomains compatible supports domains531 targets531 12 185) (childTargets supports targets531 185) :=
  transport_child domains531 targets531 12 185 domains530 targets530 (by decide) (by decide) rejected530
theorem rejected531 : ¬ Sat compatible supports domains531 targets531 :=
  refute_split compatible supports domains531 targets531 12 [180, 181, 182, 183, 184, 185] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected531_180, (List.forall_mem_cons.mpr ⟨child_rejected531_181, (List.forall_mem_cons.mpr ⟨child_rejected531_182, (List.forall_mem_cons.mpr ⟨child_rejected531_183, (List.forall_mem_cons.mpr ⟨child_rejected531_184, (List.forall_mem_cons.mpr ⟨child_rejected531_185, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected531
theorem rejected532 : ¬ Sat compatible supports domains532 targets532 :=
  refute_empty_domain compatible supports domains532 targets532 2 (by decide)
#print axioms rejected532
theorem rejected533 : ¬ Sat compatible supports domains533 targets533 :=
  refute_empty_domain compatible supports domains533 targets533 13 (by decide)
#print axioms rejected533
theorem rejected534 : ¬ Sat compatible supports domains534 targets534 :=
  refute_empty_domain compatible supports domains534 targets534 4 (by decide)
#print axioms rejected534
theorem rejected535 : ¬ Sat compatible supports domains535 targets535 :=
  refute_empty_domain compatible supports domains535 targets535 4 (by decide)
#print axioms rejected535
end ElevenSquare.Pending.EncodedSearch
