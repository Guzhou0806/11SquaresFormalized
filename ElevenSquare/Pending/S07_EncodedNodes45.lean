import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes43
import ElevenSquare.Pending.S07_EncodedNodes44
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected360_70 : ¬ Sat compatible supports (childDomains compatible supports domains360 targets360 5 70) (childTargets supports targets360 70) :=
  transport_child domains360 targets360 5 70 domains359 targets359 (by decide) (by decide) rejected359
theorem rejected360 : ¬ Sat compatible supports domains360 targets360 :=
  refute_split compatible supports domains360 targets360 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected360_70, List.forall_mem_nil _⟩)
#print axioms rejected360
set_option maxRecDepth 8192 in
theorem child_rejected361_5 : ¬ Sat compatible supports (childDomains compatible supports domains361 targets361 0 5) (childTargets supports targets361 5) :=
  transport_child domains361 targets361 0 5 domains357 targets357 (by decide) (by decide) rejected357
set_option maxRecDepth 8192 in
theorem child_rejected361_8 : ¬ Sat compatible supports (childDomains compatible supports domains361 targets361 0 8) (childTargets supports targets361 8) :=
  transport_child domains361 targets361 0 8 domains360 targets360 (by decide) (by decide) rejected360
theorem rejected361 : ¬ Sat compatible supports domains361 targets361 :=
  refute_split compatible supports domains361 targets361 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected361_5, (List.forall_mem_cons.mpr ⟨child_rejected361_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected361
set_option maxRecDepth 8192 in
theorem child_rejected362_15 : ¬ Sat compatible supports (childDomains compatible supports domains362 targets362 1 15) (childTargets supports targets362 15) :=
  transport_child domains362 targets362 1 15 domains344 targets344 (by decide) (by decide) rejected344
set_option maxRecDepth 8192 in
theorem child_rejected362_16 : ¬ Sat compatible supports (childDomains compatible supports domains362 targets362 1 16) (childTargets supports targets362 16) :=
  transport_child domains362 targets362 1 16 domains347 targets347 (by decide) (by decide) rejected347
set_option maxRecDepth 8192 in
theorem child_rejected362_18 : ¬ Sat compatible supports (childDomains compatible supports domains362 targets362 1 18) (childTargets supports targets362 18) :=
  transport_child domains362 targets362 1 18 domains354 targets354 (by decide) (by decide) rejected354
set_option maxRecDepth 8192 in
theorem child_rejected362_19 : ¬ Sat compatible supports (childDomains compatible supports domains362 targets362 1 19) (childTargets supports targets362 19) :=
  transport_child domains362 targets362 1 19 domains361 targets361 (by decide) (by decide) rejected361
theorem rejected362 : ¬ Sat compatible supports domains362 targets362 :=
  refute_split compatible supports domains362 targets362 1 [15, 16, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected362_15, (List.forall_mem_cons.mpr ⟨child_rejected362_16, (List.forall_mem_cons.mpr ⟨child_rejected362_18, (List.forall_mem_cons.mpr ⟨child_rejected362_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected362
theorem rejected363 : ¬ Sat compatible supports domains363 targets363 :=
  refute_empty_domain compatible supports domains363 targets363 13 (by decide)
#print axioms rejected363
set_option maxRecDepth 8192 in
theorem child_rejected364_206 : ¬ Sat compatible supports (childDomains compatible supports domains364 targets364 14 206) (childTargets supports targets364 206) :=
  transport_child domains364 targets364 14 206 domains363 targets363 (by decide) (by decide) rejected363
theorem rejected364 : ¬ Sat compatible supports domains364 targets364 :=
  refute_split compatible supports domains364 targets364 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected364_206, List.forall_mem_nil _⟩)
#print axioms rejected364
theorem rejected365 : ¬ Sat compatible supports domains365 targets365 :=
  refute_empty_domain compatible supports domains365 targets365 13 (by decide)
#print axioms rejected365
set_option maxRecDepth 8192 in
theorem child_rejected366_206 : ¬ Sat compatible supports (childDomains compatible supports domains366 targets366 14 206) (childTargets supports targets366 206) :=
  transport_child domains366 targets366 14 206 domains365 targets365 (by decide) (by decide) rejected365
theorem rejected366 : ¬ Sat compatible supports domains366 targets366 :=
  refute_split compatible supports domains366 targets366 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected366_206, List.forall_mem_nil _⟩)
#print axioms rejected366
set_option maxRecDepth 8192 in
theorem child_rejected367_123 : ¬ Sat compatible supports (childDomains compatible supports domains367 targets367 8 123) (childTargets supports targets367 123) :=
  transport_child domains367 targets367 8 123 domains366 targets366 (by decide) (by decide) rejected366
theorem rejected367 : ¬ Sat compatible supports domains367 targets367 :=
  refute_split compatible supports domains367 targets367 8 [123] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected367_123, List.forall_mem_nil _⟩)
#print axioms rejected367
end ElevenSquare.Pending.EncodedSearch
