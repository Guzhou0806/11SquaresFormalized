import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes8
import ElevenSquare.Pending.S07_EncodedNodes9
import ElevenSquare.Pending.S07_EncodedNodes10
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected88_23 : ¬ Sat compatible supports (childDomains compatible supports domains88 targets88 2 23) (childTargets supports targets88 23) :=
  transport_child domains88 targets88 2 23 domains87 targets87 (by decide) (by decide) rejected87
theorem rejected88 : ¬ Sat compatible supports domains88 targets88 :=
  refute_split compatible supports domains88 targets88 2 [23] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected88_23, List.forall_mem_nil _⟩)
#print axioms rejected88
set_option maxRecDepth 8192 in
theorem child_rejected89_5 : ¬ Sat compatible supports (childDomains compatible supports domains89 targets89 0 5) (childTargets supports targets89 5) :=
  transport_child domains89 targets89 0 5 domains85 targets85 (by decide) (by decide) rejected85
set_option maxRecDepth 8192 in
theorem child_rejected89_8 : ¬ Sat compatible supports (childDomains compatible supports domains89 targets89 0 8) (childTargets supports targets89 8) :=
  transport_child domains89 targets89 0 8 domains88 targets88 (by decide) (by decide) rejected88
theorem rejected89 : ¬ Sat compatible supports domains89 targets89 :=
  refute_split compatible supports domains89 targets89 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected89_5, (List.forall_mem_cons.mpr ⟨child_rejected89_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected89
theorem rejected90 : ¬ Sat compatible supports domains90 targets90 :=
  refute_empty_domain compatible supports domains90 targets90 4 (by decide)
#print axioms rejected90
theorem rejected91 : ¬ Sat compatible supports domains91 targets91 :=
  refute_empty_domain compatible supports domains91 targets91 4 (by decide)
#print axioms rejected91
set_option maxRecDepth 8192 in
theorem child_rejected92_5 : ¬ Sat compatible supports (childDomains compatible supports domains92 targets92 0 5) (childTargets supports targets92 5) :=
  transport_child domains92 targets92 0 5 domains90 targets90 (by decide) (by decide) rejected90
set_option maxRecDepth 8192 in
theorem child_rejected92_8 : ¬ Sat compatible supports (childDomains compatible supports domains92 targets92 0 8) (childTargets supports targets92 8) :=
  transport_child domains92 targets92 0 8 domains91 targets91 (by decide) (by decide) rejected91
theorem rejected92 : ¬ Sat compatible supports domains92 targets92 :=
  refute_split compatible supports domains92 targets92 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected92_5, (List.forall_mem_cons.mpr ⟨child_rejected92_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected92
set_option maxRecDepth 8192 in
theorem child_rejected93_12 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 12) (childTargets supports targets93 12) :=
  transport_child domains93 targets93 1 12 domains64 targets64 (by decide) (by decide) rejected64
set_option maxRecDepth 8192 in
theorem child_rejected93_13 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 13) (childTargets supports targets93 13) :=
  transport_child domains93 targets93 1 13 domains68 targets68 (by decide) (by decide) rejected68
set_option maxRecDepth 8192 in
theorem child_rejected93_14 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 14) (childTargets supports targets93 14) :=
  transport_child domains93 targets93 1 14 domains69 targets69 (by decide) (by decide) rejected69
set_option maxRecDepth 8192 in
theorem child_rejected93_15 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 15) (childTargets supports targets93 15) :=
  transport_child domains93 targets93 1 15 domains73 targets73 (by decide) (by decide) rejected73
set_option maxRecDepth 8192 in
theorem child_rejected93_16 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 16) (childTargets supports targets93 16) :=
  transport_child domains93 targets93 1 16 domains81 targets81 (by decide) (by decide) rejected81
set_option maxRecDepth 8192 in
theorem child_rejected93_17 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 17) (childTargets supports targets93 17) :=
  transport_child domains93 targets93 1 17 domains84 targets84 (by decide) (by decide) rejected84
set_option maxRecDepth 8192 in
theorem child_rejected93_18 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 18) (childTargets supports targets93 18) :=
  transport_child domains93 targets93 1 18 domains89 targets89 (by decide) (by decide) rejected89
set_option maxRecDepth 8192 in
theorem child_rejected93_19 : ¬ Sat compatible supports (childDomains compatible supports domains93 targets93 1 19) (childTargets supports targets93 19) :=
  transport_child domains93 targets93 1 19 domains92 targets92 (by decide) (by decide) rejected92
theorem rejected93 : ¬ Sat compatible supports domains93 targets93 :=
  refute_split compatible supports domains93 targets93 1 [12, 13, 14, 15, 16, 17, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected93_12, (List.forall_mem_cons.mpr ⟨child_rejected93_13, (List.forall_mem_cons.mpr ⟨child_rejected93_14, (List.forall_mem_cons.mpr ⟨child_rejected93_15, (List.forall_mem_cons.mpr ⟨child_rejected93_16, (List.forall_mem_cons.mpr ⟨child_rejected93_17, (List.forall_mem_cons.mpr ⟨child_rejected93_18, (List.forall_mem_cons.mpr ⟨child_rejected93_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected93
theorem rejected94 : ¬ Sat compatible supports domains94 targets94 :=
  refute_empty_domain compatible supports domains94 targets94 0 (by decide)
#print axioms rejected94
theorem rejected95 : ¬ Sat compatible supports domains95 targets95 :=
  refute_empty_domain compatible supports domains95 targets95 0 (by decide)
#print axioms rejected95
end ElevenSquare.Pending.EncodedSearch
