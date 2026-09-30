import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes4
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected40_13 : ¬ Sat compatible supports (childDomains compatible supports domains40 targets40 1 13) (childTargets supports targets40 13) :=
  transport_child domains40 targets40 1 13 domains38 targets38 (by decide) (by decide) rejected38
set_option maxRecDepth 8192 in
theorem child_rejected40_17 : ¬ Sat compatible supports (childDomains compatible supports domains40 targets40 1 17) (childTargets supports targets40 17) :=
  transport_child domains40 targets40 1 17 domains39 targets39 (by decide) (by decide) rejected39
theorem rejected40 : ¬ Sat compatible supports domains40 targets40 :=
  refute_split compatible supports domains40 targets40 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected40_13, (List.forall_mem_cons.mpr ⟨child_rejected40_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected40
theorem rejected41 : ¬ Sat compatible supports domains41 targets41 :=
  refute_empty_domain compatible supports domains41 targets41 6 (by decide)
#print axioms rejected41
set_option maxRecDepth 8192 in
theorem child_rejected42_29 : ¬ Sat compatible supports (childDomains compatible supports domains42 targets42 2 29) (childTargets supports targets42 29) :=
  transport_child domains42 targets42 2 29 domains41 targets41 (by decide) (by decide) rejected41
theorem rejected42 : ¬ Sat compatible supports domains42 targets42 :=
  refute_split compatible supports domains42 targets42 2 [29] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected42_29, List.forall_mem_nil _⟩)
#print axioms rejected42
set_option maxRecDepth 8192 in
theorem child_rejected43_13 : ¬ Sat compatible supports (childDomains compatible supports domains43 targets43 1 13) (childTargets supports targets43 13) :=
  transport_child domains43 targets43 1 13 domains42 targets42 (by decide) (by decide) rejected42
theorem rejected43 : ¬ Sat compatible supports domains43 targets43 :=
  refute_split compatible supports domains43 targets43 1 [13] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected43_13, List.forall_mem_nil _⟩)
#print axioms rejected43
set_option maxRecDepth 8192 in
theorem child_rejected44_2 : ¬ Sat compatible supports (childDomains compatible supports domains44 targets44 0 2) (childTargets supports targets44 2) :=
  transport_child domains44 targets44 0 2 domains43 targets43 (by decide) (by decide) rejected43
theorem rejected44 : ¬ Sat compatible supports domains44 targets44 :=
  refute_split compatible supports domains44 targets44 0 [2] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected44_2, List.forall_mem_nil _⟩)
#print axioms rejected44
set_option maxRecDepth 8192 in
theorem child_rejected45_149 : ¬ Sat compatible supports (childDomains compatible supports domains45 targets45 10 149) (childTargets supports targets45 149) :=
  transport_child domains45 targets45 10 149 domains44 targets44 (by decide) (by decide) rejected44
theorem rejected45 : ¬ Sat compatible supports domains45 targets45 :=
  refute_split compatible supports domains45 targets45 10 [149] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected45_149, List.forall_mem_nil _⟩)
#print axioms rejected45
theorem rejected46 : ¬ Sat compatible supports domains46 targets46 :=
  refute_empty_domain compatible supports domains46 targets46 6 (by decide)
#print axioms rejected46
set_option maxRecDepth 8192 in
theorem child_rejected47_28 : ¬ Sat compatible supports (childDomains compatible supports domains47 targets47 2 28) (childTargets supports targets47 28) :=
  transport_child domains47 targets47 2 28 domains46 targets46 (by decide) (by decide) rejected46
theorem rejected47 : ¬ Sat compatible supports domains47 targets47 :=
  refute_split compatible supports domains47 targets47 2 [28] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected47_28, List.forall_mem_nil _⟩)
#print axioms rejected47
end ElevenSquare.Pending.EncodedSearch
