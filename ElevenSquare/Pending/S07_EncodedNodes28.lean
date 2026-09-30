import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes27
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected224 : ¬ Sat compatible supports domains224 targets224 :=
  refute_empty_domain compatible supports domains224 targets224 14 (by decide)
#print axioms rejected224
theorem rejected225 : ¬ Sat compatible supports domains225 targets225 :=
  refute_empty_domain compatible supports domains225 targets225 14 (by decide)
#print axioms rejected225
set_option maxRecDepth 8192 in
theorem child_rejected226_194 : ¬ Sat compatible supports (childDomains compatible supports domains226 targets226 13 194) (childTargets supports targets226 194) :=
  transport_child domains226 targets226 13 194 domains224 targets224 (by decide) (by decide) rejected224
set_option maxRecDepth 8192 in
theorem child_rejected226_197 : ¬ Sat compatible supports (childDomains compatible supports domains226 targets226 13 197) (childTargets supports targets226 197) :=
  transport_child domains226 targets226 13 197 domains225 targets225 (by decide) (by decide) rejected225
theorem rejected226 : ¬ Sat compatible supports domains226 targets226 :=
  refute_split compatible supports domains226 targets226 13 [194, 197] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected226_194, (List.forall_mem_cons.mpr ⟨child_rejected226_197, List.forall_mem_nil _⟩)⟩)
#print axioms rejected226
set_option maxRecDepth 8192 in
theorem child_rejected227_217 : ¬ Sat compatible supports (childDomains compatible supports domains227 targets227 15 217) (childTargets supports targets227 217) :=
  transport_child domains227 targets227 15 217 domains226 targets226 (by decide) (by decide) rejected226
theorem rejected227 : ¬ Sat compatible supports domains227 targets227 :=
  refute_split compatible supports domains227 targets227 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected227_217, List.forall_mem_nil _⟩)
#print axioms rejected227
set_option maxRecDepth 8192 in
theorem child_rejected228_117 : ¬ Sat compatible supports (childDomains compatible supports domains228 targets228 8 117) (childTargets supports targets228 117) :=
  transport_child domains228 targets228 8 117 domains227 targets227 (by decide) (by decide) rejected227
theorem rejected228 : ¬ Sat compatible supports domains228 targets228 :=
  refute_split compatible supports domains228 targets228 8 [117] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected228_117, List.forall_mem_nil _⟩)
#print axioms rejected228
set_option maxRecDepth 8192 in
theorem child_rejected229_5 : ¬ Sat compatible supports (childDomains compatible supports domains229 targets229 0 5) (childTargets supports targets229 5) :=
  transport_child domains229 targets229 0 5 domains223 targets223 (by decide) (by decide) rejected223
set_option maxRecDepth 8192 in
theorem child_rejected229_8 : ¬ Sat compatible supports (childDomains compatible supports domains229 targets229 0 8) (childTargets supports targets229 8) :=
  transport_child domains229 targets229 0 8 domains228 targets228 (by decide) (by decide) rejected228
theorem rejected229 : ¬ Sat compatible supports domains229 targets229 :=
  refute_split compatible supports domains229 targets229 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected229_5, (List.forall_mem_cons.mpr ⟨child_rejected229_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected229
theorem rejected230 : ¬ Sat compatible supports domains230 targets230 :=
  refute_empty_domain compatible supports domains230 targets230 9 (by decide)
#print axioms rejected230
theorem rejected231 : ¬ Sat compatible supports domains231 targets231 :=
  refute_empty_domain compatible supports domains231 targets231 9 (by decide)
#print axioms rejected231
end ElevenSquare.Pending.EncodedSearch
