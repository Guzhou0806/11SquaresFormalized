import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes32
import ElevenSquare.Pending.S07_EncodedNodes33
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected272_143 : ¬ Sat compatible supports (childDomains compatible supports domains272 targets272 9 143) (childTargets supports targets272 143) :=
  transport_child domains272 targets272 9 143 domains271 targets271 (by decide) (by decide) rejected271
theorem rejected272 : ¬ Sat compatible supports domains272 targets272 :=
  refute_split compatible supports domains272 targets272 9 [143] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected272_143, List.forall_mem_nil _⟩)
#print axioms rejected272
theorem rejected273 : ¬ Sat compatible supports domains273 targets273 :=
  refute_empty_domain compatible supports domains273 targets273 11 (by decide)
#print axioms rejected273
set_option maxRecDepth 8192 in
theorem child_rejected274_88 : ¬ Sat compatible supports (childDomains compatible supports domains274 targets274 6 88) (childTargets supports targets274 88) :=
  transport_child domains274 targets274 6 88 domains272 targets272 (by decide) (by decide) rejected272
set_option maxRecDepth 8192 in
theorem child_rejected274_92 : ¬ Sat compatible supports (childDomains compatible supports domains274 targets274 6 92) (childTargets supports targets274 92) :=
  transport_child domains274 targets274 6 92 domains273 targets273 (by decide) (by decide) rejected273
theorem rejected274 : ¬ Sat compatible supports domains274 targets274 :=
  refute_split compatible supports domains274 targets274 6 [88, 92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected274_88, (List.forall_mem_cons.mpr ⟨child_rejected274_92, List.forall_mem_nil _⟩)⟩)
#print axioms rejected274
set_option maxRecDepth 8192 in
theorem child_rejected275_65 : ¬ Sat compatible supports (childDomains compatible supports domains275 targets275 5 65) (childTargets supports targets275 65) :=
  transport_child domains275 targets275 5 65 domains262 targets262 (by decide) (by decide) rejected262
set_option maxRecDepth 8192 in
theorem child_rejected275_68 : ¬ Sat compatible supports (childDomains compatible supports domains275 targets275 5 68) (childTargets supports targets275 68) :=
  transport_child domains275 targets275 5 68 domains268 targets268 (by decide) (by decide) rejected268
set_option maxRecDepth 8192 in
theorem child_rejected275_69 : ¬ Sat compatible supports (childDomains compatible supports domains275 targets275 5 69) (childTargets supports targets275 69) :=
  transport_child domains275 targets275 5 69 domains270 targets270 (by decide) (by decide) rejected270
set_option maxRecDepth 8192 in
theorem child_rejected275_70 : ¬ Sat compatible supports (childDomains compatible supports domains275 targets275 5 70) (childTargets supports targets275 70) :=
  transport_child domains275 targets275 5 70 domains274 targets274 (by decide) (by decide) rejected274
theorem rejected275 : ¬ Sat compatible supports domains275 targets275 :=
  refute_split compatible supports domains275 targets275 5 [65, 68, 69, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected275_65, (List.forall_mem_cons.mpr ⟨child_rejected275_68, (List.forall_mem_cons.mpr ⟨child_rejected275_69, (List.forall_mem_cons.mpr ⟨child_rejected275_70, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected275
theorem rejected276 : ¬ Sat compatible supports domains276 targets276 :=
  refute_empty_domain compatible supports domains276 targets276 5 (by decide)
#print axioms rejected276
theorem rejected277 : ¬ Sat compatible supports domains277 targets277 :=
  refute_empty_domain compatible supports domains277 targets277 5 (by decide)
#print axioms rejected277
theorem rejected278 : ¬ Sat compatible supports domains278 targets278 :=
  refute_empty_domain compatible supports domains278 targets278 5 (by decide)
#print axioms rejected278
theorem rejected279 : ¬ Sat compatible supports domains279 targets279 :=
  refute_empty_domain compatible supports domains279 targets279 14 (by decide)
#print axioms rejected279
end ElevenSquare.Pending.EncodedSearch
