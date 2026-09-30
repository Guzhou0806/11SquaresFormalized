import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes46
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected376_206 : ¬ Sat compatible supports (childDomains compatible supports domains376 targets376 14 206) (childTargets supports targets376 206) :=
  transport_child domains376 targets376 14 206 domains375 targets375 (by decide) (by decide) rejected375
theorem rejected376 : ¬ Sat compatible supports domains376 targets376 :=
  refute_split compatible supports domains376 targets376 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected376_206, List.forall_mem_nil _⟩)
#print axioms rejected376
theorem rejected377 : ¬ Sat compatible supports domains377 targets377 :=
  refute_empty_domain compatible supports domains377 targets377 13 (by decide)
#print axioms rejected377
set_option maxRecDepth 8192 in
theorem child_rejected378_206 : ¬ Sat compatible supports (childDomains compatible supports domains378 targets378 14 206) (childTargets supports targets378 206) :=
  transport_child domains378 targets378 14 206 domains377 targets377 (by decide) (by decide) rejected377
theorem rejected378 : ¬ Sat compatible supports domains378 targets378 :=
  refute_split compatible supports domains378 targets378 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected378_206, List.forall_mem_nil _⟩)
#print axioms rejected378
set_option maxRecDepth 8192 in
theorem child_rejected379_123 : ¬ Sat compatible supports (childDomains compatible supports domains379 targets379 8 123) (childTargets supports targets379 123) :=
  transport_child domains379 targets379 8 123 domains378 targets378 (by decide) (by decide) rejected378
theorem rejected379 : ¬ Sat compatible supports domains379 targets379 :=
  refute_split compatible supports domains379 targets379 8 [123] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected379_123, List.forall_mem_nil _⟩)
#print axioms rejected379
set_option maxRecDepth 8192 in
theorem child_rejected380_5 : ¬ Sat compatible supports (childDomains compatible supports domains380 targets380 0 5) (childTargets supports targets380 5) :=
  transport_child domains380 targets380 0 5 domains376 targets376 (by decide) (by decide) rejected376
set_option maxRecDepth 8192 in
theorem child_rejected380_8 : ¬ Sat compatible supports (childDomains compatible supports domains380 targets380 0 8) (childTargets supports targets380 8) :=
  transport_child domains380 targets380 0 8 domains379 targets379 (by decide) (by decide) rejected379
theorem rejected380 : ¬ Sat compatible supports domains380 targets380 :=
  refute_split compatible supports domains380 targets380 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected380_5, (List.forall_mem_cons.mpr ⟨child_rejected380_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected380
theorem rejected381 : ¬ Sat compatible supports domains381 targets381 :=
  refute_empty_domain compatible supports domains381 targets381 9 (by decide)
#print axioms rejected381
set_option maxRecDepth 8192 in
theorem child_rejected382_70 : ¬ Sat compatible supports (childDomains compatible supports domains382 targets382 5 70) (childTargets supports targets382 70) :=
  transport_child domains382 targets382 5 70 domains381 targets381 (by decide) (by decide) rejected381
theorem rejected382 : ¬ Sat compatible supports domains382 targets382 :=
  refute_split compatible supports domains382 targets382 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected382_70, List.forall_mem_nil _⟩)
#print axioms rejected382
theorem rejected383 : ¬ Sat compatible supports domains383 targets383 :=
  refute_empty_domain compatible supports domains383 targets383 9 (by decide)
#print axioms rejected383
end ElevenSquare.Pending.EncodedSearch
