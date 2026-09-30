import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes0
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected8_22 : ¬ Sat compatible supports (childDomains compatible supports domains8 targets8 2 22) (childTargets supports targets8 22) :=
  transport_child domains8 targets8 2 22 domains3 targets3 (by decide) (by decide) rejected3
set_option maxRecDepth 8192 in
theorem child_rejected8_25 : ¬ Sat compatible supports (childDomains compatible supports domains8 targets8 2 25) (childTargets supports targets8 25) :=
  transport_child domains8 targets8 2 25 domains7 targets7 (by decide) (by decide) rejected7
theorem rejected8 : ¬ Sat compatible supports domains8 targets8 :=
  refute_split compatible supports domains8 targets8 2 [22, 25] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected8_22, (List.forall_mem_cons.mpr ⟨child_rejected8_25, List.forall_mem_nil _⟩)⟩)
#print axioms rejected8
theorem rejected9 : ¬ Sat compatible supports domains9 targets9 :=
  refute_empty_domain compatible supports domains9 targets9 4 (by decide)
#print axioms rejected9
theorem rejected10 : ¬ Sat compatible supports domains10 targets10 :=
  refute_empty_domain compatible supports domains10 targets10 4 (by decide)
#print axioms rejected10
set_option maxRecDepth 8192 in
theorem child_rejected11_5 : ¬ Sat compatible supports (childDomains compatible supports domains11 targets11 0 5) (childTargets supports targets11 5) :=
  transport_child domains11 targets11 0 5 domains9 targets9 (by decide) (by decide) rejected9
set_option maxRecDepth 8192 in
theorem child_rejected11_8 : ¬ Sat compatible supports (childDomains compatible supports domains11 targets11 0 8) (childTargets supports targets11 8) :=
  transport_child domains11 targets11 0 8 domains10 targets10 (by decide) (by decide) rejected10
theorem rejected11 : ¬ Sat compatible supports domains11 targets11 :=
  refute_split compatible supports domains11 targets11 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected11_5, (List.forall_mem_cons.mpr ⟨child_rejected11_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected11
set_option maxRecDepth 8192 in
theorem child_rejected12_18 : ¬ Sat compatible supports (childDomains compatible supports domains12 targets12 1 18) (childTargets supports targets12 18) :=
  transport_child domains12 targets12 1 18 domains11 targets11 (by decide) (by decide) rejected11
theorem rejected12 : ¬ Sat compatible supports domains12 targets12 :=
  refute_split compatible supports domains12 targets12 1 [18] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected12_18, List.forall_mem_nil _⟩)
#print axioms rejected12
theorem rejected13 : ¬ Sat compatible supports domains13 targets13 :=
  refute_empty_domain compatible supports domains13 targets13 4 (by decide)
#print axioms rejected13
theorem rejected14 : ¬ Sat compatible supports domains14 targets14 :=
  refute_empty_domain compatible supports domains14 targets14 4 (by decide)
#print axioms rejected14
set_option maxRecDepth 8192 in
theorem child_rejected15_5 : ¬ Sat compatible supports (childDomains compatible supports domains15 targets15 0 5) (childTargets supports targets15 5) :=
  transport_child domains15 targets15 0 5 domains13 targets13 (by decide) (by decide) rejected13
set_option maxRecDepth 8192 in
theorem child_rejected15_8 : ¬ Sat compatible supports (childDomains compatible supports domains15 targets15 0 8) (childTargets supports targets15 8) :=
  transport_child domains15 targets15 0 8 domains14 targets14 (by decide) (by decide) rejected14
theorem rejected15 : ¬ Sat compatible supports domains15 targets15 :=
  refute_split compatible supports domains15 targets15 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected15_5, (List.forall_mem_cons.mpr ⟨child_rejected15_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected15
end ElevenSquare.Pending.EncodedSearch
