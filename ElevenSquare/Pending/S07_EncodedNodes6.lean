import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes4
import ElevenSquare.Pending.S07_EncodedNodes5
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected48_2 : ¬ Sat compatible supports (childDomains compatible supports domains48 targets48 0 2) (childTargets supports targets48 2) :=
  transport_child domains48 targets48 0 2 domains47 targets47 (by decide) (by decide) rejected47
theorem rejected48 : ¬ Sat compatible supports domains48 targets48 :=
  refute_split compatible supports domains48 targets48 0 [2] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected48_2, List.forall_mem_nil _⟩)
#print axioms rejected48
theorem rejected49 : ¬ Sat compatible supports domains49 targets49 :=
  refute_empty_domain compatible supports domains49 targets49 10 (by decide)
#print axioms rejected49
set_option maxRecDepth 8192 in
theorem child_rejected50_13 : ¬ Sat compatible supports (childDomains compatible supports domains50 targets50 1 13) (childTargets supports targets50 13) :=
  transport_child domains50 targets50 1 13 domains48 targets48 (by decide) (by decide) rejected48
set_option maxRecDepth 8192 in
theorem child_rejected50_17 : ¬ Sat compatible supports (childDomains compatible supports domains50 targets50 1 17) (childTargets supports targets50 17) :=
  transport_child domains50 targets50 1 17 domains49 targets49 (by decide) (by decide) rejected49
theorem rejected50 : ¬ Sat compatible supports domains50 targets50 :=
  refute_split compatible supports domains50 targets50 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected50_13, (List.forall_mem_cons.mpr ⟨child_rejected50_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected50
set_option maxRecDepth 8192 in
theorem child_rejected51_200 : ¬ Sat compatible supports (childDomains compatible supports domains51 targets51 14 200) (childTargets supports targets51 200) :=
  transport_child domains51 targets51 14 200 domains36 targets36 (by decide) (by decide) rejected36
set_option maxRecDepth 8192 in
theorem child_rejected51_201 : ¬ Sat compatible supports (childDomains compatible supports domains51 targets51 14 201) (childTargets supports targets51 201) :=
  transport_child domains51 targets51 14 201 domains40 targets40 (by decide) (by decide) rejected40
set_option maxRecDepth 8192 in
theorem child_rejected51_203 : ¬ Sat compatible supports (childDomains compatible supports domains51 targets51 14 203) (childTargets supports targets51 203) :=
  transport_child domains51 targets51 14 203 domains45 targets45 (by decide) (by decide) rejected45
set_option maxRecDepth 8192 in
theorem child_rejected51_204 : ¬ Sat compatible supports (childDomains compatible supports domains51 targets51 14 204) (childTargets supports targets51 204) :=
  transport_child domains51 targets51 14 204 domains50 targets50 (by decide) (by decide) rejected50
theorem rejected51 : ¬ Sat compatible supports domains51 targets51 :=
  refute_split compatible supports domains51 targets51 14 [200, 201, 203, 204] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected51_200, (List.forall_mem_cons.mpr ⟨child_rejected51_201, (List.forall_mem_cons.mpr ⟨child_rejected51_203, (List.forall_mem_cons.mpr ⟨child_rejected51_204, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected51
theorem rejected52 : ¬ Sat compatible supports domains52 targets52 :=
  refute_empty_domain compatible supports domains52 targets52 2 (by decide)
#print axioms rejected52
set_option maxRecDepth 8192 in
theorem child_rejected53_2 : ¬ Sat compatible supports (childDomains compatible supports domains53 targets53 0 2) (childTargets supports targets53 2) :=
  transport_child domains53 targets53 0 2 domains52 targets52 (by decide) (by decide) rejected52
theorem rejected53 : ¬ Sat compatible supports domains53 targets53 :=
  refute_split compatible supports domains53 targets53 0 [2] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected53_2, List.forall_mem_nil _⟩)
#print axioms rejected53
theorem rejected54 : ¬ Sat compatible supports domains54 targets54 :=
  refute_empty_domain compatible supports domains54 targets54 0 (by decide)
#print axioms rejected54
theorem rejected55 : ¬ Sat compatible supports domains55 targets55 :=
  refute_empty_domain compatible supports domains55 targets55 0 (by decide)
#print axioms rejected55
end ElevenSquare.Pending.EncodedSearch
