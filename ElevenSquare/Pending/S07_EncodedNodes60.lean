import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected480 : ¬ Sat compatible supports domains480 targets480 :=
  refute_empty_domain compatible supports domains480 targets480 2 (by decide)
#print axioms rejected480
theorem rejected481 : ¬ Sat compatible supports domains481 targets481 :=
  refute_empty_domain compatible supports domains481 targets481 2 (by decide)
#print axioms rejected481
theorem rejected482 : ¬ Sat compatible supports domains482 targets482 :=
  refute_empty_domain compatible supports domains482 targets482 2 (by decide)
#print axioms rejected482
theorem rejected483 : ¬ Sat compatible supports domains483 targets483 :=
  refute_empty_domain compatible supports domains483 targets483 4 (by decide)
#print axioms rejected483
set_option maxRecDepth 8192 in
theorem child_rejected484_127 : ¬ Sat compatible supports (childDomains compatible supports domains484 targets484 9 127) (childTargets supports targets484 127) :=
  transport_child domains484 targets484 9 127 domains483 targets483 (by decide) (by decide) rejected483
theorem rejected484 : ¬ Sat compatible supports domains484 targets484 :=
  refute_split compatible supports domains484 targets484 9 [127] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected484_127, List.forall_mem_nil _⟩)
#print axioms rejected484
set_option maxRecDepth 8192 in
theorem child_rejected485_96 : ¬ Sat compatible supports (childDomains compatible supports domains485 targets485 7 96) (childTargets supports targets485 96) :=
  transport_child domains485 targets485 7 96 domains484 targets484 (by decide) (by decide) rejected484
theorem rejected485 : ¬ Sat compatible supports domains485 targets485 :=
  refute_split compatible supports domains485 targets485 7 [96] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected485_96, List.forall_mem_nil _⟩)
#print axioms rejected485
set_option maxRecDepth 8192 in
theorem child_rejected486_91 : ¬ Sat compatible supports (childDomains compatible supports domains486 targets486 6 91) (childTargets supports targets486 91) :=
  transport_child domains486 targets486 6 91 domains485 targets485 (by decide) (by decide) rejected485
theorem rejected486 : ¬ Sat compatible supports domains486 targets486 :=
  refute_split compatible supports domains486 targets486 6 [91] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected486_91, List.forall_mem_nil _⟩)
#print axioms rejected486
theorem rejected487 : ¬ Sat compatible supports domains487 targets487 :=
  refute_empty_domain compatible supports domains487 targets487 6 (by decide)
#print axioms rejected487
end ElevenSquare.Pending.EncodedSearch
