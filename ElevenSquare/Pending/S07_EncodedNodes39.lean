import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes38
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected312 : ¬ Sat compatible supports domains312 targets312 :=
  refute_empty_domain compatible supports domains312 targets312 14 (by decide)
#print axioms rejected312
set_option maxRecDepth 8192 in
theorem child_rejected313_65 : ¬ Sat compatible supports (childDomains compatible supports domains313 targets313 5 65) (childTargets supports targets313 65) :=
  transport_child domains313 targets313 5 65 domains311 targets311 (by decide) (by decide) rejected311
set_option maxRecDepth 8192 in
theorem child_rejected313_70 : ¬ Sat compatible supports (childDomains compatible supports domains313 targets313 5 70) (childTargets supports targets313 70) :=
  transport_child domains313 targets313 5 70 domains312 targets312 (by decide) (by decide) rejected312
theorem rejected313 : ¬ Sat compatible supports domains313 targets313 :=
  refute_split compatible supports domains313 targets313 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected313_65, (List.forall_mem_cons.mpr ⟨child_rejected313_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected313
theorem rejected314 : ¬ Sat compatible supports domains314 targets314 :=
  refute_empty_domain compatible supports domains314 targets314 5 (by decide)
#print axioms rejected314
theorem rejected315 : ¬ Sat compatible supports domains315 targets315 :=
  refute_empty_domain compatible supports domains315 targets315 14 (by decide)
#print axioms rejected315
theorem rejected316 : ¬ Sat compatible supports domains316 targets316 :=
  refute_empty_domain compatible supports domains316 targets316 6 (by decide)
#print axioms rejected316
theorem rejected317 : ¬ Sat compatible supports domains317 targets317 :=
  refute_empty_domain compatible supports domains317 targets317 6 (by decide)
#print axioms rejected317
set_option maxRecDepth 8192 in
theorem child_rejected318_65 : ¬ Sat compatible supports (childDomains compatible supports domains318 targets318 5 65) (childTargets supports targets318 65) :=
  transport_child domains318 targets318 5 65 domains316 targets316 (by decide) (by decide) rejected316
set_option maxRecDepth 8192 in
theorem child_rejected318_70 : ¬ Sat compatible supports (childDomains compatible supports domains318 targets318 5 70) (childTargets supports targets318 70) :=
  transport_child domains318 targets318 5 70 domains317 targets317 (by decide) (by decide) rejected317
theorem rejected318 : ¬ Sat compatible supports domains318 targets318 :=
  refute_split compatible supports domains318 targets318 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected318_65, (List.forall_mem_cons.mpr ⟨child_rejected318_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected318
set_option maxRecDepth 8192 in
theorem child_rejected319_216 : ¬ Sat compatible supports (childDomains compatible supports domains319 targets319 15 216) (childTargets supports targets319 216) :=
  transport_child domains319 targets319 15 216 domains313 targets313 (by decide) (by decide) rejected313
set_option maxRecDepth 8192 in
theorem child_rejected319_217 : ¬ Sat compatible supports (childDomains compatible supports domains319 targets319 15 217) (childTargets supports targets319 217) :=
  transport_child domains319 targets319 15 217 domains314 targets314 (by decide) (by decide) rejected314
set_option maxRecDepth 8192 in
theorem child_rejected319_218 : ¬ Sat compatible supports (childDomains compatible supports domains319 targets319 15 218) (childTargets supports targets319 218) :=
  transport_child domains319 targets319 15 218 domains315 targets315 (by decide) (by decide) rejected315
set_option maxRecDepth 8192 in
theorem child_rejected319_219 : ¬ Sat compatible supports (childDomains compatible supports domains319 targets319 15 219) (childTargets supports targets319 219) :=
  transport_child domains319 targets319 15 219 domains318 targets318 (by decide) (by decide) rejected318
theorem rejected319 : ¬ Sat compatible supports domains319 targets319 :=
  refute_split compatible supports domains319 targets319 15 [216, 217, 218, 219] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected319_216, (List.forall_mem_cons.mpr ⟨child_rejected319_217, (List.forall_mem_cons.mpr ⟨child_rejected319_218, (List.forall_mem_cons.mpr ⟨child_rejected319_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected319
end ElevenSquare.Pending.EncodedSearch
