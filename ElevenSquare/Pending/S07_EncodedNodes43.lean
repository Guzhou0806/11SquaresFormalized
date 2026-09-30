import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes42
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected344_5 : ¬ Sat compatible supports (childDomains compatible supports domains344 targets344 0 5) (childTargets supports targets344 5) :=
  transport_child domains344 targets344 0 5 domains340 targets340 (by decide) (by decide) rejected340
set_option maxRecDepth 8192 in
theorem child_rejected344_8 : ¬ Sat compatible supports (childDomains compatible supports domains344 targets344 0 8) (childTargets supports targets344 8) :=
  transport_child domains344 targets344 0 8 domains343 targets343 (by decide) (by decide) rejected343
theorem rejected344 : ¬ Sat compatible supports domains344 targets344 :=
  refute_split compatible supports domains344 targets344 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected344_5, (List.forall_mem_cons.mpr ⟨child_rejected344_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected344
theorem rejected345 : ¬ Sat compatible supports domains345 targets345 :=
  refute_empty_domain compatible supports domains345 targets345 11 (by decide)
#print axioms rejected345
set_option maxRecDepth 8192 in
theorem child_rejected346_92 : ¬ Sat compatible supports (childDomains compatible supports domains346 targets346 6 92) (childTargets supports targets346 92) :=
  transport_child domains346 targets346 6 92 domains345 targets345 (by decide) (by decide) rejected345
theorem rejected346 : ¬ Sat compatible supports domains346 targets346 :=
  refute_split compatible supports domains346 targets346 6 [92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected346_92, List.forall_mem_nil _⟩)
#print axioms rejected346
set_option maxRecDepth 8192 in
theorem child_rejected347_70 : ¬ Sat compatible supports (childDomains compatible supports domains347 targets347 5 70) (childTargets supports targets347 70) :=
  transport_child domains347 targets347 5 70 domains346 targets346 (by decide) (by decide) rejected346
theorem rejected347 : ¬ Sat compatible supports domains347 targets347 :=
  refute_split compatible supports domains347 targets347 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected347_70, List.forall_mem_nil _⟩)
#print axioms rejected347
theorem rejected348 : ¬ Sat compatible supports domains348 targets348 :=
  refute_empty_domain compatible supports domains348 targets348 9 (by decide)
#print axioms rejected348
set_option maxRecDepth 8192 in
theorem child_rejected349_191 : ¬ Sat compatible supports (childDomains compatible supports domains349 targets349 13 191) (childTargets supports targets349 191) :=
  transport_child domains349 targets349 13 191 domains348 targets348 (by decide) (by decide) rejected348
theorem rejected349 : ¬ Sat compatible supports domains349 targets349 :=
  refute_split compatible supports domains349 targets349 13 [191] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected349_191, List.forall_mem_nil _⟩)
#print axioms rejected349
set_option maxRecDepth 8192 in
theorem child_rejected350_206 : ¬ Sat compatible supports (childDomains compatible supports domains350 targets350 14 206) (childTargets supports targets350 206) :=
  transport_child domains350 targets350 14 206 domains349 targets349 (by decide) (by decide) rejected349
theorem rejected350 : ¬ Sat compatible supports domains350 targets350 :=
  refute_split compatible supports domains350 targets350 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected350_206, List.forall_mem_nil _⟩)
#print axioms rejected350
theorem rejected351 : ¬ Sat compatible supports domains351 targets351 :=
  refute_empty_domain compatible supports domains351 targets351 9 (by decide)
#print axioms rejected351
end ElevenSquare.Pending.EncodedSearch
