import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes48
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected392 : ¬ Sat compatible supports domains392 targets392 :=
  refute_empty_domain compatible supports domains392 targets392 5 (by decide)
#print axioms rejected392
set_option maxRecDepth 8192 in
theorem child_rejected393_13 : ¬ Sat compatible supports (childDomains compatible supports domains393 targets393 1 13) (childTargets supports targets393 13) :=
  transport_child domains393 targets393 1 13 domains391 targets391 (by decide) (by decide) rejected391
set_option maxRecDepth 8192 in
theorem child_rejected393_17 : ¬ Sat compatible supports (childDomains compatible supports domains393 targets393 1 17) (childTargets supports targets393 17) :=
  transport_child domains393 targets393 1 17 domains392 targets392 (by decide) (by decide) rejected392
theorem rejected393 : ¬ Sat compatible supports domains393 targets393 :=
  refute_split compatible supports domains393 targets393 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected393_13, (List.forall_mem_cons.mpr ⟨child_rejected393_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected393
set_option maxRecDepth 8192 in
theorem child_rejected394_201 : ¬ Sat compatible supports (childDomains compatible supports domains394 targets394 14 201) (childTargets supports targets394 201) :=
  transport_child domains394 targets394 14 201 domains393 targets393 (by decide) (by decide) rejected393
theorem rejected394 : ¬ Sat compatible supports domains394 targets394 :=
  refute_split compatible supports domains394 targets394 14 [201] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected394_201, List.forall_mem_nil _⟩)
#print axioms rejected394
set_option maxRecDepth 8192 in
theorem child_rejected395_194 : ¬ Sat compatible supports (childDomains compatible supports domains395 targets395 13 194) (childTargets supports targets395 194) :=
  transport_child domains395 targets395 13 194 domains390 targets390 (by decide) (by decide) rejected390
set_option maxRecDepth 8192 in
theorem child_rejected395_197 : ¬ Sat compatible supports (childDomains compatible supports domains395 targets395 13 197) (childTargets supports targets395 197) :=
  transport_child domains395 targets395 13 197 domains394 targets394 (by decide) (by decide) rejected394
theorem rejected395 : ¬ Sat compatible supports domains395 targets395 :=
  refute_split compatible supports domains395 targets395 13 [194, 197] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected395_194, (List.forall_mem_cons.mpr ⟨child_rejected395_197, List.forall_mem_nil _⟩)⟩)
#print axioms rejected395
theorem rejected396 : ¬ Sat compatible supports domains396 targets396 :=
  refute_empty_domain compatible supports domains396 targets396 0 (by decide)
#print axioms rejected396
theorem rejected397 : ¬ Sat compatible supports domains397 targets397 :=
  refute_empty_domain compatible supports domains397 targets397 5 (by decide)
#print axioms rejected397
set_option maxRecDepth 8192 in
theorem child_rejected398_13 : ¬ Sat compatible supports (childDomains compatible supports domains398 targets398 1 13) (childTargets supports targets398 13) :=
  transport_child domains398 targets398 1 13 domains396 targets396 (by decide) (by decide) rejected396
set_option maxRecDepth 8192 in
theorem child_rejected398_17 : ¬ Sat compatible supports (childDomains compatible supports domains398 targets398 1 17) (childTargets supports targets398 17) :=
  transport_child domains398 targets398 1 17 domains397 targets397 (by decide) (by decide) rejected397
theorem rejected398 : ¬ Sat compatible supports domains398 targets398 :=
  refute_split compatible supports domains398 targets398 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected398_13, (List.forall_mem_cons.mpr ⟨child_rejected398_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected398
set_option maxRecDepth 8192 in
theorem child_rejected399_201 : ¬ Sat compatible supports (childDomains compatible supports domains399 targets399 14 201) (childTargets supports targets399 201) :=
  transport_child domains399 targets399 14 201 domains398 targets398 (by decide) (by decide) rejected398
theorem rejected399 : ¬ Sat compatible supports domains399 targets399 :=
  refute_split compatible supports domains399 targets399 14 [201] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected399_201, List.forall_mem_nil _⟩)
#print axioms rejected399
end ElevenSquare.Pending.EncodedSearch
