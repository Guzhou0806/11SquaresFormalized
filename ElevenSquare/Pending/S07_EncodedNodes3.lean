import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected24 : ¬ Sat compatible supports domains24 targets24 :=
  refute_empty_domain compatible supports domains24 targets24 1 (by decide)
#print axioms rejected24
set_option maxRecDepth 8192 in
theorem child_rejected25_3 : ¬ Sat compatible supports (childDomains compatible supports domains25 targets25 0 3) (childTargets supports targets25 3) :=
  transport_child domains25 targets25 0 3 domains24 targets24 (by decide) (by decide) rejected24
theorem rejected25 : ¬ Sat compatible supports domains25 targets25 :=
  refute_split compatible supports domains25 targets25 0 [3] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected25_3, List.forall_mem_nil _⟩)
#print axioms rejected25
set_option maxRecDepth 8192 in
theorem child_rejected26_149 : ¬ Sat compatible supports (childDomains compatible supports domains26 targets26 10 149) (childTargets supports targets26 149) :=
  transport_child domains26 targets26 10 149 domains25 targets25 (by decide) (by decide) rejected25
theorem rejected26 : ¬ Sat compatible supports domains26 targets26 :=
  refute_split compatible supports domains26 targets26 10 [149] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected26_149, List.forall_mem_nil _⟩)
#print axioms rejected26
theorem rejected27 : ¬ Sat compatible supports domains27 targets27 :=
  refute_empty_domain compatible supports domains27 targets27 6 (by decide)
#print axioms rejected27
set_option maxRecDepth 8192 in
theorem child_rejected28_149 : ¬ Sat compatible supports (childDomains compatible supports domains28 targets28 10 149) (childTargets supports targets28 149) :=
  transport_child domains28 targets28 10 149 domains27 targets27 (by decide) (by decide) rejected27
theorem rejected28 : ¬ Sat compatible supports domains28 targets28 :=
  refute_split compatible supports domains28 targets28 10 [149] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected28_149, List.forall_mem_nil _⟩)
#print axioms rejected28
theorem rejected29 : ¬ Sat compatible supports domains29 targets29 :=
  refute_empty_domain compatible supports domains29 targets29 2 (by decide)
#print axioms rejected29
theorem rejected30 : ¬ Sat compatible supports domains30 targets30 :=
  refute_empty_domain compatible supports domains30 targets30 2 (by decide)
#print axioms rejected30
set_option maxRecDepth 8192 in
theorem child_rejected31_13 : ¬ Sat compatible supports (childDomains compatible supports domains31 targets31 1 13) (childTargets supports targets31 13) :=
  transport_child domains31 targets31 1 13 domains29 targets29 (by decide) (by decide) rejected29
set_option maxRecDepth 8192 in
theorem child_rejected31_17 : ¬ Sat compatible supports (childDomains compatible supports domains31 targets31 1 17) (childTargets supports targets31 17) :=
  transport_child domains31 targets31 1 17 domains30 targets30 (by decide) (by decide) rejected30
theorem rejected31 : ¬ Sat compatible supports domains31 targets31 :=
  refute_split compatible supports domains31 targets31 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected31_13, (List.forall_mem_cons.mpr ⟨child_rejected31_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected31
end ElevenSquare.Pending.EncodedSearch
