import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes56
import ElevenSquare.Pending.S07_EncodedNodes59
import ElevenSquare.Pending.S07_EncodedNodes61
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected496_34 : ¬ Sat compatible supports (childDomains compatible supports domains496 targets496 3 34) (childTargets supports targets496 34) :=
  transport_child domains496 targets496 3 34 domains454 targets454 (by decide) (by decide) rejected454
set_option maxRecDepth 8192 in
theorem child_rejected496_35 : ¬ Sat compatible supports (childDomains compatible supports domains496 targets496 3 35) (childTargets supports targets496 35) :=
  transport_child domains496 targets496 3 35 domains478 targets478 (by decide) (by decide) rejected478
set_option maxRecDepth 8192 in
theorem child_rejected496_36 : ¬ Sat compatible supports (childDomains compatible supports domains496 targets496 3 36) (childTargets supports targets496 36) :=
  transport_child domains496 targets496 3 36 domains479 targets479 (by decide) (by decide) rejected479
set_option maxRecDepth 8192 in
theorem child_rejected496_37 : ¬ Sat compatible supports (childDomains compatible supports domains496 targets496 3 37) (childTargets supports targets496 37) :=
  transport_child domains496 targets496 3 37 domains493 targets493 (by decide) (by decide) rejected493
set_option maxRecDepth 8192 in
theorem child_rejected496_38 : ¬ Sat compatible supports (childDomains compatible supports domains496 targets496 3 38) (childTargets supports targets496 38) :=
  transport_child domains496 targets496 3 38 domains494 targets494 (by decide) (by decide) rejected494
set_option maxRecDepth 8192 in
theorem child_rejected496_39 : ¬ Sat compatible supports (childDomains compatible supports domains496 targets496 3 39) (childTargets supports targets496 39) :=
  transport_child domains496 targets496 3 39 domains495 targets495 (by decide) (by decide) rejected495
theorem rejected496 : ¬ Sat compatible supports domains496 targets496 :=
  refute_split compatible supports domains496 targets496 3 [34, 35, 36, 37, 38, 39] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected496_34, (List.forall_mem_cons.mpr ⟨child_rejected496_35, (List.forall_mem_cons.mpr ⟨child_rejected496_36, (List.forall_mem_cons.mpr ⟨child_rejected496_37, (List.forall_mem_cons.mpr ⟨child_rejected496_38, (List.forall_mem_cons.mpr ⟨child_rejected496_39, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected496
theorem rejected497 : ¬ Sat compatible supports domains497 targets497 :=
  refute_empty_domain compatible supports domains497 targets497 13 (by decide)
#print axioms rejected497
theorem rejected498 : ¬ Sat compatible supports domains498 targets498 :=
  refute_empty_domain compatible supports domains498 targets498 4 (by decide)
#print axioms rejected498
theorem rejected499 : ¬ Sat compatible supports domains499 targets499 :=
  refute_empty_domain compatible supports domains499 targets499 4 (by decide)
#print axioms rejected499
theorem rejected500 : ¬ Sat compatible supports domains500 targets500 :=
  refute_empty_domain compatible supports domains500 targets500 4 (by decide)
#print axioms rejected500
set_option maxRecDepth 8192 in
theorem child_rejected501_111 : ¬ Sat compatible supports (childDomains compatible supports domains501 targets501 8 111) (childTargets supports targets501 111) :=
  transport_child domains501 targets501 8 111 domains497 targets497 (by decide) (by decide) rejected497
set_option maxRecDepth 8192 in
theorem child_rejected501_115 : ¬ Sat compatible supports (childDomains compatible supports domains501 targets501 8 115) (childTargets supports targets501 115) :=
  transport_child domains501 targets501 8 115 domains498 targets498 (by decide) (by decide) rejected498
set_option maxRecDepth 8192 in
theorem child_rejected501_116 : ¬ Sat compatible supports (childDomains compatible supports domains501 targets501 8 116) (childTargets supports targets501 116) :=
  transport_child domains501 targets501 8 116 domains499 targets499 (by decide) (by decide) rejected499
set_option maxRecDepth 8192 in
theorem child_rejected501_118 : ¬ Sat compatible supports (childDomains compatible supports domains501 targets501 8 118) (childTargets supports targets501 118) :=
  transport_child domains501 targets501 8 118 domains500 targets500 (by decide) (by decide) rejected500
theorem rejected501 : ¬ Sat compatible supports domains501 targets501 :=
  refute_split compatible supports domains501 targets501 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected501_111, (List.forall_mem_cons.mpr ⟨child_rejected501_115, (List.forall_mem_cons.mpr ⟨child_rejected501_116, (List.forall_mem_cons.mpr ⟨child_rejected501_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected501
set_option maxRecDepth 8192 in
theorem child_rejected502_184 : ¬ Sat compatible supports (childDomains compatible supports domains502 targets502 12 184) (childTargets supports targets502 184) :=
  transport_child domains502 targets502 12 184 domains501 targets501 (by decide) (by decide) rejected501
theorem rejected502 : ¬ Sat compatible supports domains502 targets502 :=
  refute_split compatible supports domains502 targets502 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected502_184, List.forall_mem_nil _⟩)
#print axioms rejected502
theorem rejected503 : ¬ Sat compatible supports domains503 targets503 :=
  refute_empty_domain compatible supports domains503 targets503 8 (by decide)
#print axioms rejected503
end ElevenSquare.Pending.EncodedSearch
