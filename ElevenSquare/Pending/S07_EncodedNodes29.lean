import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes23
import ElevenSquare.Pending.S07_EncodedNodes24
import ElevenSquare.Pending.S07_EncodedNodes25
import ElevenSquare.Pending.S07_EncodedNodes26
import ElevenSquare.Pending.S07_EncodedNodes27
import ElevenSquare.Pending.S07_EncodedNodes28
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected232_65 : ¬ Sat compatible supports (childDomains compatible supports domains232 targets232 5 65) (childTargets supports targets232 65) :=
  transport_child domains232 targets232 5 65 domains230 targets230 (by decide) (by decide) rejected230
set_option maxRecDepth 8192 in
theorem child_rejected232_70 : ¬ Sat compatible supports (childDomains compatible supports domains232 targets232 5 70) (childTargets supports targets232 70) :=
  transport_child domains232 targets232 5 70 domains231 targets231 (by decide) (by decide) rejected231
theorem rejected232 : ¬ Sat compatible supports domains232 targets232 :=
  refute_split compatible supports domains232 targets232 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected232_65, (List.forall_mem_cons.mpr ⟨child_rejected232_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected232
set_option maxRecDepth 8192 in
theorem child_rejected233_217 : ¬ Sat compatible supports (childDomains compatible supports domains233 targets233 15 217) (childTargets supports targets233 217) :=
  transport_child domains233 targets233 15 217 domains232 targets232 (by decide) (by decide) rejected232
theorem rejected233 : ¬ Sat compatible supports domains233 targets233 :=
  refute_split compatible supports domains233 targets233 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected233_217, List.forall_mem_nil _⟩)
#print axioms rejected233
theorem rejected234 : ¬ Sat compatible supports domains234 targets234 :=
  refute_empty_domain compatible supports domains234 targets234 9 (by decide)
#print axioms rejected234
theorem rejected235 : ¬ Sat compatible supports domains235 targets235 :=
  refute_empty_domain compatible supports domains235 targets235 9 (by decide)
#print axioms rejected235
set_option maxRecDepth 8192 in
theorem child_rejected236_65 : ¬ Sat compatible supports (childDomains compatible supports domains236 targets236 5 65) (childTargets supports targets236 65) :=
  transport_child domains236 targets236 5 65 domains234 targets234 (by decide) (by decide) rejected234
set_option maxRecDepth 8192 in
theorem child_rejected236_70 : ¬ Sat compatible supports (childDomains compatible supports domains236 targets236 5 70) (childTargets supports targets236 70) :=
  transport_child domains236 targets236 5 70 domains235 targets235 (by decide) (by decide) rejected235
theorem rejected236 : ¬ Sat compatible supports domains236 targets236 :=
  refute_split compatible supports domains236 targets236 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected236_65, (List.forall_mem_cons.mpr ⟨child_rejected236_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected236
set_option maxRecDepth 8192 in
theorem child_rejected237_217 : ¬ Sat compatible supports (childDomains compatible supports domains237 targets237 15 217) (childTargets supports targets237 217) :=
  transport_child domains237 targets237 15 217 domains236 targets236 (by decide) (by decide) rejected236
theorem rejected237 : ¬ Sat compatible supports domains237 targets237 :=
  refute_split compatible supports domains237 targets237 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected237_217, List.forall_mem_nil _⟩)
#print axioms rejected237
set_option maxRecDepth 8192 in
theorem child_rejected238_5 : ¬ Sat compatible supports (childDomains compatible supports domains238 targets238 0 5) (childTargets supports targets238 5) :=
  transport_child domains238 targets238 0 5 domains233 targets233 (by decide) (by decide) rejected233
set_option maxRecDepth 8192 in
theorem child_rejected238_8 : ¬ Sat compatible supports (childDomains compatible supports domains238 targets238 0 8) (childTargets supports targets238 8) :=
  transport_child domains238 targets238 0 8 domains237 targets237 (by decide) (by decide) rejected237
theorem rejected238 : ¬ Sat compatible supports domains238 targets238 :=
  refute_split compatible supports domains238 targets238 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected238_5, (List.forall_mem_cons.mpr ⟨child_rejected238_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected238
set_option maxRecDepth 8192 in
theorem child_rejected239_12 : ¬ Sat compatible supports (childDomains compatible supports domains239 targets239 1 12) (childTargets supports targets239 12) :=
  transport_child domains239 targets239 1 12 domains188 targets188 (by decide) (by decide) rejected188
set_option maxRecDepth 8192 in
theorem child_rejected239_13 : ¬ Sat compatible supports (childDomains compatible supports domains239 targets239 1 13) (childTargets supports targets239 13) :=
  transport_child domains239 targets239 1 13 domains193 targets193 (by decide) (by decide) rejected193
set_option maxRecDepth 8192 in
theorem child_rejected239_15 : ¬ Sat compatible supports (childDomains compatible supports domains239 targets239 1 15) (childTargets supports targets239 15) :=
  transport_child domains239 targets239 1 15 domains204 targets204 (by decide) (by decide) rejected204
set_option maxRecDepth 8192 in
theorem child_rejected239_16 : ¬ Sat compatible supports (childDomains compatible supports domains239 targets239 1 16) (childTargets supports targets239 16) :=
  transport_child domains239 targets239 1 16 domains212 targets212 (by decide) (by decide) rejected212
set_option maxRecDepth 8192 in
theorem child_rejected239_17 : ¬ Sat compatible supports (childDomains compatible supports domains239 targets239 1 17) (childTargets supports targets239 17) :=
  transport_child domains239 targets239 1 17 domains218 targets218 (by decide) (by decide) rejected218
set_option maxRecDepth 8192 in
theorem child_rejected239_18 : ¬ Sat compatible supports (childDomains compatible supports domains239 targets239 1 18) (childTargets supports targets239 18) :=
  transport_child domains239 targets239 1 18 domains229 targets229 (by decide) (by decide) rejected229
set_option maxRecDepth 8192 in
theorem child_rejected239_19 : ¬ Sat compatible supports (childDomains compatible supports domains239 targets239 1 19) (childTargets supports targets239 19) :=
  transport_child domains239 targets239 1 19 domains238 targets238 (by decide) (by decide) rejected238
theorem rejected239 : ¬ Sat compatible supports domains239 targets239 :=
  refute_split compatible supports domains239 targets239 1 [12, 13, 15, 16, 17, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected239_12, (List.forall_mem_cons.mpr ⟨child_rejected239_13, (List.forall_mem_cons.mpr ⟨child_rejected239_15, (List.forall_mem_cons.mpr ⟨child_rejected239_16, (List.forall_mem_cons.mpr ⟨child_rejected239_17, (List.forall_mem_cons.mpr ⟨child_rejected239_18, (List.forall_mem_cons.mpr ⟨child_rejected239_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected239
end ElevenSquare.Pending.EncodedSearch
