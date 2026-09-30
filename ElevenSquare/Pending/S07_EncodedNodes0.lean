import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected0 : ¬ Sat compatible supports domains0 targets0 :=
  refute_empty_domain compatible supports domains0 targets0 4 (by decide)
#print axioms rejected0
theorem rejected1 : ¬ Sat compatible supports domains1 targets1 :=
  refute_empty_domain compatible supports domains1 targets1 4 (by decide)
#print axioms rejected1
set_option maxRecDepth 8192 in
theorem child_rejected2_5 : ¬ Sat compatible supports (childDomains compatible supports domains2 targets2 0 5) (childTargets supports targets2 5) :=
  transport_child domains2 targets2 0 5 domains0 targets0 (by decide) (by decide) rejected0
set_option maxRecDepth 8192 in
theorem child_rejected2_8 : ¬ Sat compatible supports (childDomains compatible supports domains2 targets2 0 8) (childTargets supports targets2 8) :=
  transport_child domains2 targets2 0 8 domains1 targets1 (by decide) (by decide) rejected1
theorem rejected2 : ¬ Sat compatible supports domains2 targets2 :=
  refute_split compatible supports domains2 targets2 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected2_5, (List.forall_mem_cons.mpr ⟨child_rejected2_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected2
set_option maxRecDepth 8192 in
theorem child_rejected3_18 : ¬ Sat compatible supports (childDomains compatible supports domains3 targets3 1 18) (childTargets supports targets3 18) :=
  transport_child domains3 targets3 1 18 domains2 targets2 (by decide) (by decide) rejected2
theorem rejected3 : ¬ Sat compatible supports domains3 targets3 :=
  refute_split compatible supports domains3 targets3 1 [18] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected3_18, List.forall_mem_nil _⟩)
#print axioms rejected3
theorem rejected4 : ¬ Sat compatible supports domains4 targets4 :=
  refute_empty_domain compatible supports domains4 targets4 4 (by decide)
#print axioms rejected4
theorem rejected5 : ¬ Sat compatible supports domains5 targets5 :=
  refute_empty_domain compatible supports domains5 targets5 4 (by decide)
#print axioms rejected5
set_option maxRecDepth 8192 in
theorem child_rejected6_5 : ¬ Sat compatible supports (childDomains compatible supports domains6 targets6 0 5) (childTargets supports targets6 5) :=
  transport_child domains6 targets6 0 5 domains4 targets4 (by decide) (by decide) rejected4
set_option maxRecDepth 8192 in
theorem child_rejected6_8 : ¬ Sat compatible supports (childDomains compatible supports domains6 targets6 0 8) (childTargets supports targets6 8) :=
  transport_child domains6 targets6 0 8 domains5 targets5 (by decide) (by decide) rejected5
theorem rejected6 : ¬ Sat compatible supports domains6 targets6 :=
  refute_split compatible supports domains6 targets6 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected6_5, (List.forall_mem_cons.mpr ⟨child_rejected6_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected6
set_option maxRecDepth 8192 in
theorem child_rejected7_18 : ¬ Sat compatible supports (childDomains compatible supports domains7 targets7 1 18) (childTargets supports targets7 18) :=
  transport_child domains7 targets7 1 18 domains6 targets6 (by decide) (by decide) rejected6
theorem rejected7 : ¬ Sat compatible supports domains7 targets7 :=
  refute_split compatible supports domains7 targets7 1 [18] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected7_18, List.forall_mem_nil _⟩)
#print axioms rejected7
end ElevenSquare.Pending.EncodedSearch
