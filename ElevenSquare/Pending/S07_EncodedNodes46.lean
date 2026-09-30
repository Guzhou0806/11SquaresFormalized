import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes45
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected368_5 : ¬ Sat compatible supports (childDomains compatible supports domains368 targets368 0 5) (childTargets supports targets368 5) :=
  transport_child domains368 targets368 0 5 domains364 targets364 (by decide) (by decide) rejected364
set_option maxRecDepth 8192 in
theorem child_rejected368_8 : ¬ Sat compatible supports (childDomains compatible supports domains368 targets368 0 8) (childTargets supports targets368 8) :=
  transport_child domains368 targets368 0 8 domains367 targets367 (by decide) (by decide) rejected367
theorem rejected368 : ¬ Sat compatible supports domains368 targets368 :=
  refute_split compatible supports domains368 targets368 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected368_5, (List.forall_mem_cons.mpr ⟨child_rejected368_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected368
theorem rejected369 : ¬ Sat compatible supports domains369 targets369 :=
  refute_empty_domain compatible supports domains369 targets369 9 (by decide)
#print axioms rejected369
set_option maxRecDepth 8192 in
theorem child_rejected370_70 : ¬ Sat compatible supports (childDomains compatible supports domains370 targets370 5 70) (childTargets supports targets370 70) :=
  transport_child domains370 targets370 5 70 domains369 targets369 (by decide) (by decide) rejected369
theorem rejected370 : ¬ Sat compatible supports domains370 targets370 :=
  refute_split compatible supports domains370 targets370 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected370_70, List.forall_mem_nil _⟩)
#print axioms rejected370
theorem rejected371 : ¬ Sat compatible supports domains371 targets371 :=
  refute_empty_domain compatible supports domains371 targets371 13 (by decide)
#print axioms rejected371
set_option maxRecDepth 8192 in
theorem child_rejected372_140 : ¬ Sat compatible supports (childDomains compatible supports domains372 targets372 9 140) (childTargets supports targets372 140) :=
  transport_child domains372 targets372 9 140 domains371 targets371 (by decide) (by decide) rejected371
theorem rejected372 : ¬ Sat compatible supports domains372 targets372 :=
  refute_split compatible supports domains372 targets372 9 [140] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected372_140, List.forall_mem_nil _⟩)
#print axioms rejected372
set_option maxRecDepth 8192 in
theorem child_rejected373_8 : ¬ Sat compatible supports (childDomains compatible supports domains373 targets373 0 8) (childTargets supports targets373 8) :=
  transport_child domains373 targets373 0 8 domains372 targets372 (by decide) (by decide) rejected372
theorem rejected373 : ¬ Sat compatible supports domains373 targets373 :=
  refute_split compatible supports domains373 targets373 0 [8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected373_8, List.forall_mem_nil _⟩)
#print axioms rejected373
set_option maxRecDepth 8192 in
theorem child_rejected374_70 : ¬ Sat compatible supports (childDomains compatible supports domains374 targets374 5 70) (childTargets supports targets374 70) :=
  transport_child domains374 targets374 5 70 domains373 targets373 (by decide) (by decide) rejected373
theorem rejected374 : ¬ Sat compatible supports domains374 targets374 :=
  refute_split compatible supports domains374 targets374 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected374_70, List.forall_mem_nil _⟩)
#print axioms rejected374
theorem rejected375 : ¬ Sat compatible supports domains375 targets375 :=
  refute_empty_domain compatible supports domains375 targets375 13 (by decide)
#print axioms rejected375
end ElevenSquare.Pending.EncodedSearch
