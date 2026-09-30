import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes31
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected256_201 : ¬ Sat compatible supports (childDomains compatible supports domains256 targets256 14 201) (childTargets supports targets256 201) :=
  transport_child domains256 targets256 14 201 domains254 targets254 (by decide) (by decide) rejected254
set_option maxRecDepth 8192 in
theorem child_rejected256_204 : ¬ Sat compatible supports (childDomains compatible supports domains256 targets256 14 204) (childTargets supports targets256 204) :=
  transport_child domains256 targets256 14 204 domains255 targets255 (by decide) (by decide) rejected255
theorem rejected256 : ¬ Sat compatible supports domains256 targets256 :=
  refute_split compatible supports domains256 targets256 14 [201, 204] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected256_201, (List.forall_mem_cons.mpr ⟨child_rejected256_204, List.forall_mem_nil _⟩)⟩)
#print axioms rejected256
theorem rejected257 : ¬ Sat compatible supports domains257 targets257 :=
  refute_empty_domain compatible supports domains257 targets257 15 (by decide)
#print axioms rejected257
set_option maxRecDepth 8192 in
theorem child_rejected258_204 : ¬ Sat compatible supports (childDomains compatible supports domains258 targets258 14 204) (childTargets supports targets258 204) :=
  transport_child domains258 targets258 14 204 domains257 targets257 (by decide) (by decide) rejected257
theorem rejected258 : ¬ Sat compatible supports domains258 targets258 :=
  refute_split compatible supports domains258 targets258 14 [204] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected258_204, List.forall_mem_nil _⟩)
#print axioms rejected258
set_option maxRecDepth 8192 in
theorem child_rejected259_195 : ¬ Sat compatible supports (childDomains compatible supports domains259 targets259 13 195) (childTargets supports targets259 195) :=
  transport_child domains259 targets259 13 195 domains256 targets256 (by decide) (by decide) rejected256
set_option maxRecDepth 8192 in
theorem child_rejected259_198 : ¬ Sat compatible supports (childDomains compatible supports domains259 targets259 13 198) (childTargets supports targets259 198) :=
  transport_child domains259 targets259 13 198 domains258 targets258 (by decide) (by decide) rejected258
theorem rejected259 : ¬ Sat compatible supports domains259 targets259 :=
  refute_split compatible supports domains259 targets259 13 [195, 198] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected259_195, (List.forall_mem_cons.mpr ⟨child_rejected259_198, List.forall_mem_nil _⟩)⟩)
#print axioms rejected259
set_option maxRecDepth 8192 in
theorem child_rejected260_175 : ¬ Sat compatible supports (childDomains compatible supports domains260 targets260 11 175) (childTargets supports targets260 175) :=
  transport_child domains260 targets260 11 175 domains253 targets253 (by decide) (by decide) rejected253
set_option maxRecDepth 8192 in
theorem child_rejected260_177 : ¬ Sat compatible supports (childDomains compatible supports domains260 targets260 11 177) (childTargets supports targets260 177) :=
  transport_child domains260 targets260 11 177 domains259 targets259 (by decide) (by decide) rejected259
theorem rejected260 : ¬ Sat compatible supports domains260 targets260 :=
  refute_split compatible supports domains260 targets260 11 [175, 177] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected260_175, (List.forall_mem_cons.mpr ⟨child_rejected260_177, List.forall_mem_nil _⟩)⟩)
#print axioms rejected260
theorem rejected261 : ¬ Sat compatible supports domains261 targets261 :=
  refute_empty_domain compatible supports domains261 targets261 11 (by decide)
#print axioms rejected261
set_option maxRecDepth 8192 in
theorem child_rejected262_88 : ¬ Sat compatible supports (childDomains compatible supports domains262 targets262 6 88) (childTargets supports targets262 88) :=
  transport_child domains262 targets262 6 88 domains260 targets260 (by decide) (by decide) rejected260
set_option maxRecDepth 8192 in
theorem child_rejected262_92 : ¬ Sat compatible supports (childDomains compatible supports domains262 targets262 6 92) (childTargets supports targets262 92) :=
  transport_child domains262 targets262 6 92 domains261 targets261 (by decide) (by decide) rejected261
theorem rejected262 : ¬ Sat compatible supports domains262 targets262 :=
  refute_split compatible supports domains262 targets262 6 [88, 92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected262_88, (List.forall_mem_cons.mpr ⟨child_rejected262_92, List.forall_mem_nil _⟩)⟩)
#print axioms rejected262
theorem rejected263 : ¬ Sat compatible supports domains263 targets263 :=
  refute_empty_domain compatible supports domains263 targets263 15 (by decide)
#print axioms rejected263
end ElevenSquare.Pending.EncodedSearch
