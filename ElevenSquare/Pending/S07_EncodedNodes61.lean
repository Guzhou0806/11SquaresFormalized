import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes60
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected488_26 : ¬ Sat compatible supports (childDomains compatible supports domains488 targets488 2 26) (childTargets supports targets488 26) :=
  transport_child domains488 targets488 2 26 domains486 targets486 (by decide) (by decide) rejected486
set_option maxRecDepth 8192 in
theorem child_rejected488_28 : ¬ Sat compatible supports (childDomains compatible supports domains488 targets488 2 28) (childTargets supports targets488 28) :=
  transport_child domains488 targets488 2 28 domains487 targets487 (by decide) (by decide) rejected487
theorem rejected488 : ¬ Sat compatible supports domains488 targets488 :=
  refute_split compatible supports domains488 targets488 2 [26, 28] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected488_26, (List.forall_mem_cons.mpr ⟨child_rejected488_28, List.forall_mem_nil _⟩)⟩)
#print axioms rejected488
theorem rejected489 : ¬ Sat compatible supports domains489 targets489 :=
  refute_empty_domain compatible supports domains489 targets489 9 (by decide)
#print axioms rejected489
theorem rejected490 : ¬ Sat compatible supports domains490 targets490 :=
  refute_empty_domain compatible supports domains490 targets490 6 (by decide)
#print axioms rejected490
set_option maxRecDepth 8192 in
theorem child_rejected491_26 : ¬ Sat compatible supports (childDomains compatible supports domains491 targets491 2 26) (childTargets supports targets491 26) :=
  transport_child domains491 targets491 2 26 domains489 targets489 (by decide) (by decide) rejected489
set_option maxRecDepth 8192 in
theorem child_rejected491_28 : ¬ Sat compatible supports (childDomains compatible supports domains491 targets491 2 28) (childTargets supports targets491 28) :=
  transport_child domains491 targets491 2 28 domains490 targets490 (by decide) (by decide) rejected490
theorem rejected491 : ¬ Sat compatible supports domains491 targets491 :=
  refute_split compatible supports domains491 targets491 2 [26, 28] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected491_26, (List.forall_mem_cons.mpr ⟨child_rejected491_28, List.forall_mem_nil _⟩)⟩)
#print axioms rejected491
set_option maxRecDepth 8192 in
theorem child_rejected492_15 : ¬ Sat compatible supports (childDomains compatible supports domains492 targets492 1 15) (childTargets supports targets492 15) :=
  transport_child domains492 targets492 1 15 domains480 targets480 (by decide) (by decide) rejected480
set_option maxRecDepth 8192 in
theorem child_rejected492_16 : ¬ Sat compatible supports (childDomains compatible supports domains492 targets492 1 16) (childTargets supports targets492 16) :=
  transport_child domains492 targets492 1 16 domains481 targets481 (by decide) (by decide) rejected481
set_option maxRecDepth 8192 in
theorem child_rejected492_17 : ¬ Sat compatible supports (childDomains compatible supports domains492 targets492 1 17) (childTargets supports targets492 17) :=
  transport_child domains492 targets492 1 17 domains482 targets482 (by decide) (by decide) rejected482
set_option maxRecDepth 8192 in
theorem child_rejected492_18 : ¬ Sat compatible supports (childDomains compatible supports domains492 targets492 1 18) (childTargets supports targets492 18) :=
  transport_child domains492 targets492 1 18 domains488 targets488 (by decide) (by decide) rejected488
set_option maxRecDepth 8192 in
theorem child_rejected492_19 : ¬ Sat compatible supports (childDomains compatible supports domains492 targets492 1 19) (childTargets supports targets492 19) :=
  transport_child domains492 targets492 1 19 domains491 targets491 (by decide) (by decide) rejected491
theorem rejected492 : ¬ Sat compatible supports domains492 targets492 :=
  refute_split compatible supports domains492 targets492 1 [15, 16, 17, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected492_15, (List.forall_mem_cons.mpr ⟨child_rejected492_16, (List.forall_mem_cons.mpr ⟨child_rejected492_17, (List.forall_mem_cons.mpr ⟨child_rejected492_18, (List.forall_mem_cons.mpr ⟨child_rejected492_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
#print axioms rejected492
set_option maxRecDepth 8192 in
theorem child_rejected493_184 : ¬ Sat compatible supports (childDomains compatible supports domains493 targets493 12 184) (childTargets supports targets493 184) :=
  transport_child domains493 targets493 12 184 domains492 targets492 (by decide) (by decide) rejected492
theorem rejected493 : ¬ Sat compatible supports domains493 targets493 :=
  refute_split compatible supports domains493 targets493 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected493_184, List.forall_mem_nil _⟩)
#print axioms rejected493
theorem rejected494 : ¬ Sat compatible supports domains494 targets494 :=
  refute_empty_domain compatible supports domains494 targets494 2 (by decide)
#print axioms rejected494
theorem rejected495 : ¬ Sat compatible supports domains495 targets495 :=
  refute_empty_domain compatible supports domains495 targets495 2 (by decide)
#print axioms rejected495
end ElevenSquare.Pending.EncodedSearch
