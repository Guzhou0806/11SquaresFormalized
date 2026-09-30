import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes46
import ElevenSquare.Pending.S07_EncodedNodes47
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected384_70 : ¬ Sat compatible supports (childDomains compatible supports domains384 targets384 5 70) (childTargets supports targets384 70) :=
  transport_child domains384 targets384 5 70 domains383 targets383 (by decide) (by decide) rejected383
theorem rejected384 : ¬ Sat compatible supports domains384 targets384 :=
  refute_split compatible supports domains384 targets384 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected384_70, List.forall_mem_nil _⟩)
#print axioms rejected384
set_option maxRecDepth 8192 in
theorem child_rejected385_5 : ¬ Sat compatible supports (childDomains compatible supports domains385 targets385 0 5) (childTargets supports targets385 5) :=
  transport_child domains385 targets385 0 5 domains382 targets382 (by decide) (by decide) rejected382
set_option maxRecDepth 8192 in
theorem child_rejected385_8 : ¬ Sat compatible supports (childDomains compatible supports domains385 targets385 0 8) (childTargets supports targets385 8) :=
  transport_child domains385 targets385 0 8 domains384 targets384 (by decide) (by decide) rejected384
theorem rejected385 : ¬ Sat compatible supports domains385 targets385 :=
  refute_split compatible supports domains385 targets385 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected385_5, (List.forall_mem_cons.mpr ⟨child_rejected385_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected385
set_option maxRecDepth 8192 in
theorem child_rejected386_15 : ¬ Sat compatible supports (childDomains compatible supports domains386 targets386 1 15) (childTargets supports targets386 15) :=
  transport_child domains386 targets386 1 15 domains368 targets368 (by decide) (by decide) rejected368
set_option maxRecDepth 8192 in
theorem child_rejected386_16 : ¬ Sat compatible supports (childDomains compatible supports domains386 targets386 1 16) (childTargets supports targets386 16) :=
  transport_child domains386 targets386 1 16 domains370 targets370 (by decide) (by decide) rejected370
set_option maxRecDepth 8192 in
theorem child_rejected386_17 : ¬ Sat compatible supports (childDomains compatible supports domains386 targets386 1 17) (childTargets supports targets386 17) :=
  transport_child domains386 targets386 1 17 domains374 targets374 (by decide) (by decide) rejected374
set_option maxRecDepth 8192 in
theorem child_rejected386_18 : ¬ Sat compatible supports (childDomains compatible supports domains386 targets386 1 18) (childTargets supports targets386 18) :=
  transport_child domains386 targets386 1 18 domains380 targets380 (by decide) (by decide) rejected380
set_option maxRecDepth 8192 in
theorem child_rejected386_19 : ¬ Sat compatible supports (childDomains compatible supports domains386 targets386 1 19) (childTargets supports targets386 19) :=
  transport_child domains386 targets386 1 19 domains385 targets385 (by decide) (by decide) rejected385
theorem rejected386 : ¬ Sat compatible supports domains386 targets386 :=
  refute_split compatible supports domains386 targets386 1 [15, 16, 17, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected386_15, (List.forall_mem_cons.mpr ⟨child_rejected386_16, (List.forall_mem_cons.mpr ⟨child_rejected386_17, (List.forall_mem_cons.mpr ⟨child_rejected386_18, (List.forall_mem_cons.mpr ⟨child_rejected386_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
#print axioms rejected386
theorem rejected387 : ¬ Sat compatible supports domains387 targets387 :=
  refute_empty_domain compatible supports domains387 targets387 0 (by decide)
#print axioms rejected387
theorem rejected388 : ¬ Sat compatible supports domains388 targets388 :=
  refute_empty_domain compatible supports domains388 targets388 5 (by decide)
#print axioms rejected388
set_option maxRecDepth 8192 in
theorem child_rejected389_13 : ¬ Sat compatible supports (childDomains compatible supports domains389 targets389 1 13) (childTargets supports targets389 13) :=
  transport_child domains389 targets389 1 13 domains387 targets387 (by decide) (by decide) rejected387
set_option maxRecDepth 8192 in
theorem child_rejected389_17 : ¬ Sat compatible supports (childDomains compatible supports domains389 targets389 1 17) (childTargets supports targets389 17) :=
  transport_child domains389 targets389 1 17 domains388 targets388 (by decide) (by decide) rejected388
theorem rejected389 : ¬ Sat compatible supports domains389 targets389 :=
  refute_split compatible supports domains389 targets389 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected389_13, (List.forall_mem_cons.mpr ⟨child_rejected389_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected389
set_option maxRecDepth 8192 in
theorem child_rejected390_201 : ¬ Sat compatible supports (childDomains compatible supports domains390 targets390 14 201) (childTargets supports targets390 201) :=
  transport_child domains390 targets390 14 201 domains389 targets389 (by decide) (by decide) rejected389
theorem rejected390 : ¬ Sat compatible supports domains390 targets390 :=
  refute_split compatible supports domains390 targets390 14 [201] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected390_201, List.forall_mem_nil _⟩)
#print axioms rejected390
theorem rejected391 : ¬ Sat compatible supports domains391 targets391 :=
  refute_empty_domain compatible supports domains391 targets391 0 (by decide)
#print axioms rejected391
end ElevenSquare.Pending.EncodedSearch
