import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes1
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected16_18 : ¬ Sat compatible supports (childDomains compatible supports domains16 targets16 1 18) (childTargets supports targets16 18) :=
  transport_child domains16 targets16 1 18 domains15 targets15 (by decide) (by decide) rejected15
theorem rejected16 : ¬ Sat compatible supports domains16 targets16 :=
  refute_split compatible supports domains16 targets16 1 [18] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected16_18, List.forall_mem_nil _⟩)
#print axioms rejected16
set_option maxRecDepth 8192 in
theorem child_rejected17_22 : ¬ Sat compatible supports (childDomains compatible supports domains17 targets17 2 22) (childTargets supports targets17 22) :=
  transport_child domains17 targets17 2 22 domains12 targets12 (by decide) (by decide) rejected12
set_option maxRecDepth 8192 in
theorem child_rejected17_25 : ¬ Sat compatible supports (childDomains compatible supports domains17 targets17 2 25) (childTargets supports targets17 25) :=
  transport_child domains17 targets17 2 25 domains16 targets16 (by decide) (by decide) rejected16
theorem rejected17 : ¬ Sat compatible supports domains17 targets17 :=
  refute_split compatible supports domains17 targets17 2 [22, 25] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected17_22, (List.forall_mem_cons.mpr ⟨child_rejected17_25, List.forall_mem_nil _⟩)⟩)
#print axioms rejected17
theorem rejected18 : ¬ Sat compatible supports domains18 targets18 :=
  refute_empty_domain compatible supports domains18 targets18 2 (by decide)
#print axioms rejected18
theorem rejected19 : ¬ Sat compatible supports domains19 targets19 :=
  refute_empty_domain compatible supports domains19 targets19 2 (by decide)
#print axioms rejected19
set_option maxRecDepth 8192 in
theorem child_rejected20_13 : ¬ Sat compatible supports (childDomains compatible supports domains20 targets20 1 13) (childTargets supports targets20 13) :=
  transport_child domains20 targets20 1 13 domains18 targets18 (by decide) (by decide) rejected18
set_option maxRecDepth 8192 in
theorem child_rejected20_17 : ¬ Sat compatible supports (childDomains compatible supports domains20 targets20 1 17) (childTargets supports targets20 17) :=
  transport_child domains20 targets20 1 17 domains19 targets19 (by decide) (by decide) rejected19
theorem rejected20 : ¬ Sat compatible supports domains20 targets20 :=
  refute_split compatible supports domains20 targets20 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected20_13, (List.forall_mem_cons.mpr ⟨child_rejected20_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected20
theorem rejected21 : ¬ Sat compatible supports domains21 targets21 :=
  refute_empty_domain compatible supports domains21 targets21 2 (by decide)
#print axioms rejected21
theorem rejected22 : ¬ Sat compatible supports domains22 targets22 :=
  refute_empty_domain compatible supports domains22 targets22 2 (by decide)
#print axioms rejected22
set_option maxRecDepth 8192 in
theorem child_rejected23_13 : ¬ Sat compatible supports (childDomains compatible supports domains23 targets23 1 13) (childTargets supports targets23 13) :=
  transport_child domains23 targets23 1 13 domains21 targets21 (by decide) (by decide) rejected21
set_option maxRecDepth 8192 in
theorem child_rejected23_17 : ¬ Sat compatible supports (childDomains compatible supports domains23 targets23 1 17) (childTargets supports targets23 17) :=
  transport_child domains23 targets23 1 17 domains22 targets22 (by decide) (by decide) rejected22
theorem rejected23 : ¬ Sat compatible supports domains23 targets23 :=
  refute_split compatible supports domains23 targets23 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected23_13, (List.forall_mem_cons.mpr ⟨child_rejected23_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected23
end ElevenSquare.Pending.EncodedSearch
