import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected448 : ¬ Sat compatible supports domains448 targets448 :=
  refute_empty_domain compatible supports domains448 targets448 2 (by decide)
#print axioms rejected448
theorem rejected449 : ¬ Sat compatible supports domains449 targets449 :=
  refute_empty_domain compatible supports domains449 targets449 1 (by decide)
#print axioms rejected449
set_option maxRecDepth 8192 in
theorem child_rejected450_25 : ¬ Sat compatible supports (childDomains compatible supports domains450 targets450 2 25) (childTargets supports targets450 25) :=
  transport_child domains450 targets450 2 25 domains449 targets449 (by decide) (by decide) rejected449
theorem rejected450 : ¬ Sat compatible supports domains450 targets450 :=
  refute_split compatible supports domains450 targets450 2 [25] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected450_25, List.forall_mem_nil _⟩)
#print axioms rejected450
theorem rejected451 : ¬ Sat compatible supports domains451 targets451 :=
  refute_empty_domain compatible supports domains451 targets451 2 (by decide)
#print axioms rejected451
theorem rejected452 : ¬ Sat compatible supports domains452 targets452 :=
  refute_empty_domain compatible supports domains452 targets452 2 (by decide)
#print axioms rejected452
set_option maxRecDepth 8192 in
theorem child_rejected453_101 : ¬ Sat compatible supports (childDomains compatible supports domains453 targets453 7 101) (childTargets supports targets453 101) :=
  transport_child domains453 targets453 7 101 domains448 targets448 (by decide) (by decide) rejected448
set_option maxRecDepth 8192 in
theorem child_rejected453_103 : ¬ Sat compatible supports (childDomains compatible supports domains453 targets453 7 103) (childTargets supports targets453 103) :=
  transport_child domains453 targets453 7 103 domains450 targets450 (by decide) (by decide) rejected450
set_option maxRecDepth 8192 in
theorem child_rejected453_104 : ¬ Sat compatible supports (childDomains compatible supports domains453 targets453 7 104) (childTargets supports targets453 104) :=
  transport_child domains453 targets453 7 104 domains451 targets451 (by decide) (by decide) rejected451
set_option maxRecDepth 8192 in
theorem child_rejected453_108 : ¬ Sat compatible supports (childDomains compatible supports domains453 targets453 7 108) (childTargets supports targets453 108) :=
  transport_child domains453 targets453 7 108 domains452 targets452 (by decide) (by decide) rejected452
theorem rejected453 : ¬ Sat compatible supports domains453 targets453 :=
  refute_split compatible supports domains453 targets453 7 [101, 103, 104, 108] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected453_101, (List.forall_mem_cons.mpr ⟨child_rejected453_103, (List.forall_mem_cons.mpr ⟨child_rejected453_104, (List.forall_mem_cons.mpr ⟨child_rejected453_108, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected453
set_option maxRecDepth 8192 in
theorem child_rejected454_184 : ¬ Sat compatible supports (childDomains compatible supports domains454 targets454 12 184) (childTargets supports targets454 184) :=
  transport_child domains454 targets454 12 184 domains453 targets453 (by decide) (by decide) rejected453
theorem rejected454 : ¬ Sat compatible supports domains454 targets454 :=
  refute_split compatible supports domains454 targets454 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected454_184, List.forall_mem_nil _⟩)
#print axioms rejected454
theorem rejected455 : ¬ Sat compatible supports domains455 targets455 :=
  refute_empty_domain compatible supports domains455 targets455 12 (by decide)
#print axioms rejected455
end ElevenSquare.Pending.EncodedSearch
