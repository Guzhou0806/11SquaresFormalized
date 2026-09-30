import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes34
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected280_70 : ¬ Sat compatible supports (childDomains compatible supports domains280 targets280 5 70) (childTargets supports targets280 70) :=
  transport_child domains280 targets280 5 70 domains279 targets279 (by decide) (by decide) rejected279
theorem rejected280 : ¬ Sat compatible supports domains280 targets280 :=
  refute_split compatible supports domains280 targets280 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected280_70, List.forall_mem_nil _⟩)
#print axioms rejected280
theorem rejected281 : ¬ Sat compatible supports domains281 targets281 :=
  refute_empty_domain compatible supports domains281 targets281 5 (by decide)
#print axioms rejected281
set_option maxRecDepth 8192 in
theorem child_rejected282_216 : ¬ Sat compatible supports (childDomains compatible supports domains282 targets282 15 216) (childTargets supports targets282 216) :=
  transport_child domains282 targets282 15 216 domains280 targets280 (by decide) (by decide) rejected280
set_option maxRecDepth 8192 in
theorem child_rejected282_217 : ¬ Sat compatible supports (childDomains compatible supports domains282 targets282 15 217) (childTargets supports targets282 217) :=
  transport_child domains282 targets282 15 217 domains281 targets281 (by decide) (by decide) rejected281
theorem rejected282 : ¬ Sat compatible supports domains282 targets282 :=
  refute_split compatible supports domains282 targets282 15 [216, 217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected282_216, (List.forall_mem_cons.mpr ⟨child_rejected282_217, List.forall_mem_nil _⟩)⟩)
#print axioms rejected282
theorem rejected283 : ¬ Sat compatible supports domains283 targets283 :=
  refute_empty_domain compatible supports domains283 targets283 14 (by decide)
#print axioms rejected283
set_option maxRecDepth 8192 in
theorem child_rejected284_216 : ¬ Sat compatible supports (childDomains compatible supports domains284 targets284 15 216) (childTargets supports targets284 216) :=
  transport_child domains284 targets284 15 216 domains283 targets283 (by decide) (by decide) rejected283
theorem rejected284 : ¬ Sat compatible supports domains284 targets284 :=
  refute_split compatible supports domains284 targets284 15 [216] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected284_216, List.forall_mem_nil _⟩)
#print axioms rejected284
set_option maxRecDepth 8192 in
theorem child_rejected285_70 : ¬ Sat compatible supports (childDomains compatible supports domains285 targets285 5 70) (childTargets supports targets285 70) :=
  transport_child domains285 targets285 5 70 domains284 targets284 (by decide) (by decide) rejected284
theorem rejected285 : ¬ Sat compatible supports domains285 targets285 :=
  refute_split compatible supports domains285 targets285 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected285_70, List.forall_mem_nil _⟩)
#print axioms rejected285
theorem rejected286 : ¬ Sat compatible supports domains286 targets286 :=
  refute_empty_domain compatible supports domains286 targets286 5 (by decide)
#print axioms rejected286
set_option maxRecDepth 8192 in
theorem child_rejected287_2 : ¬ Sat compatible supports (childDomains compatible supports domains287 targets287 0 2) (childTargets supports targets287 2) :=
  transport_child domains287 targets287 0 2 domains275 targets275 (by decide) (by decide) rejected275
set_option maxRecDepth 8192 in
theorem child_rejected287_4 : ¬ Sat compatible supports (childDomains compatible supports domains287 targets287 0 4) (childTargets supports targets287 4) :=
  transport_child domains287 targets287 0 4 domains276 targets276 (by decide) (by decide) rejected276
set_option maxRecDepth 8192 in
theorem child_rejected287_5 : ¬ Sat compatible supports (childDomains compatible supports domains287 targets287 0 5) (childTargets supports targets287 5) :=
  transport_child domains287 targets287 0 5 domains277 targets277 (by decide) (by decide) rejected277
set_option maxRecDepth 8192 in
theorem child_rejected287_6 : ¬ Sat compatible supports (childDomains compatible supports domains287 targets287 0 6) (childTargets supports targets287 6) :=
  transport_child domains287 targets287 0 6 domains278 targets278 (by decide) (by decide) rejected278
set_option maxRecDepth 8192 in
theorem child_rejected287_7 : ¬ Sat compatible supports (childDomains compatible supports domains287 targets287 0 7) (childTargets supports targets287 7) :=
  transport_child domains287 targets287 0 7 domains282 targets282 (by decide) (by decide) rejected282
set_option maxRecDepth 8192 in
theorem child_rejected287_8 : ¬ Sat compatible supports (childDomains compatible supports domains287 targets287 0 8) (childTargets supports targets287 8) :=
  transport_child domains287 targets287 0 8 domains285 targets285 (by decide) (by decide) rejected285
set_option maxRecDepth 8192 in
theorem child_rejected287_9 : ¬ Sat compatible supports (childDomains compatible supports domains287 targets287 0 9) (childTargets supports targets287 9) :=
  transport_child domains287 targets287 0 9 domains286 targets286 (by decide) (by decide) rejected286
theorem rejected287 : ¬ Sat compatible supports domains287 targets287 :=
  refute_split compatible supports domains287 targets287 0 [2, 4, 5, 6, 7, 8, 9] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected287_2, (List.forall_mem_cons.mpr ⟨child_rejected287_4, (List.forall_mem_cons.mpr ⟨child_rejected287_5, (List.forall_mem_cons.mpr ⟨child_rejected287_6, (List.forall_mem_cons.mpr ⟨child_rejected287_7, (List.forall_mem_cons.mpr ⟨child_rejected287_8, (List.forall_mem_cons.mpr ⟨child_rejected287_9, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected287
end ElevenSquare.Pending.EncodedSearch
