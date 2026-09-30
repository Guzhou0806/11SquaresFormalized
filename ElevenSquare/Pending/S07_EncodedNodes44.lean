import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes43
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected352_191 : ¬ Sat compatible supports (childDomains compatible supports domains352 targets352 13 191) (childTargets supports targets352 191) :=
  transport_child domains352 targets352 13 191 domains351 targets351 (by decide) (by decide) rejected351
theorem rejected352 : ¬ Sat compatible supports domains352 targets352 :=
  refute_split compatible supports domains352 targets352 13 [191] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected352_191, List.forall_mem_nil _⟩)
#print axioms rejected352
set_option maxRecDepth 8192 in
theorem child_rejected353_206 : ¬ Sat compatible supports (childDomains compatible supports domains353 targets353 14 206) (childTargets supports targets353 206) :=
  transport_child domains353 targets353 14 206 domains352 targets352 (by decide) (by decide) rejected352
theorem rejected353 : ¬ Sat compatible supports domains353 targets353 :=
  refute_split compatible supports domains353 targets353 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected353_206, List.forall_mem_nil _⟩)
#print axioms rejected353
set_option maxRecDepth 8192 in
theorem child_rejected354_5 : ¬ Sat compatible supports (childDomains compatible supports domains354 targets354 0 5) (childTargets supports targets354 5) :=
  transport_child domains354 targets354 0 5 domains350 targets350 (by decide) (by decide) rejected350
set_option maxRecDepth 8192 in
theorem child_rejected354_8 : ¬ Sat compatible supports (childDomains compatible supports domains354 targets354 0 8) (childTargets supports targets354 8) :=
  transport_child domains354 targets354 0 8 domains353 targets353 (by decide) (by decide) rejected353
theorem rejected354 : ¬ Sat compatible supports domains354 targets354 :=
  refute_split compatible supports domains354 targets354 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected354_5, (List.forall_mem_cons.mpr ⟨child_rejected354_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected354
theorem rejected355 : ¬ Sat compatible supports domains355 targets355 :=
  refute_empty_domain compatible supports domains355 targets355 11 (by decide)
#print axioms rejected355
set_option maxRecDepth 8192 in
theorem child_rejected356_92 : ¬ Sat compatible supports (childDomains compatible supports domains356 targets356 6 92) (childTargets supports targets356 92) :=
  transport_child domains356 targets356 6 92 domains355 targets355 (by decide) (by decide) rejected355
theorem rejected356 : ¬ Sat compatible supports domains356 targets356 :=
  refute_split compatible supports domains356 targets356 6 [92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected356_92, List.forall_mem_nil _⟩)
#print axioms rejected356
set_option maxRecDepth 8192 in
theorem child_rejected357_70 : ¬ Sat compatible supports (childDomains compatible supports domains357 targets357 5 70) (childTargets supports targets357 70) :=
  transport_child domains357 targets357 5 70 domains356 targets356 (by decide) (by decide) rejected356
theorem rejected357 : ¬ Sat compatible supports domains357 targets357 :=
  refute_split compatible supports domains357 targets357 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected357_70, List.forall_mem_nil _⟩)
#print axioms rejected357
theorem rejected358 : ¬ Sat compatible supports domains358 targets358 :=
  refute_empty_domain compatible supports domains358 targets358 11 (by decide)
#print axioms rejected358
set_option maxRecDepth 8192 in
theorem child_rejected359_92 : ¬ Sat compatible supports (childDomains compatible supports domains359 targets359 6 92) (childTargets supports targets359 92) :=
  transport_child domains359 targets359 6 92 domains358 targets358 (by decide) (by decide) rejected358
theorem rejected359 : ¬ Sat compatible supports domains359 targets359 :=
  refute_split compatible supports domains359 targets359 6 [92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected359_92, List.forall_mem_nil _⟩)
#print axioms rejected359
end ElevenSquare.Pending.EncodedSearch
