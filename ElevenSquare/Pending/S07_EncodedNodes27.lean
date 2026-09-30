import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes26
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected216_190 : ¬ Sat compatible supports (childDomains compatible supports domains216 targets216 13 190) (childTargets supports targets216 190) :=
  transport_child domains216 targets216 13 190 domains215 targets215 (by decide) (by decide) rejected215
theorem rejected216 : ¬ Sat compatible supports domains216 targets216 :=
  refute_split compatible supports domains216 targets216 13 [190] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected216_190, List.forall_mem_nil _⟩)
#print axioms rejected216
set_option maxRecDepth 8192 in
theorem child_rejected217_65 : ¬ Sat compatible supports (childDomains compatible supports domains217 targets217 5 65) (childTargets supports targets217 65) :=
  transport_child domains217 targets217 5 65 domains214 targets214 (by decide) (by decide) rejected214
set_option maxRecDepth 8192 in
theorem child_rejected217_70 : ¬ Sat compatible supports (childDomains compatible supports domains217 targets217 5 70) (childTargets supports targets217 70) :=
  transport_child domains217 targets217 5 70 domains216 targets216 (by decide) (by decide) rejected216
theorem rejected217 : ¬ Sat compatible supports domains217 targets217 :=
  refute_split compatible supports domains217 targets217 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected217_65, (List.forall_mem_cons.mpr ⟨child_rejected217_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected217
set_option maxRecDepth 8192 in
theorem child_rejected218_5 : ¬ Sat compatible supports (childDomains compatible supports domains218 targets218 0 5) (childTargets supports targets218 5) :=
  transport_child domains218 targets218 0 5 domains213 targets213 (by decide) (by decide) rejected213
set_option maxRecDepth 8192 in
theorem child_rejected218_8 : ¬ Sat compatible supports (childDomains compatible supports domains218 targets218 0 8) (childTargets supports targets218 8) :=
  transport_child domains218 targets218 0 8 domains217 targets217 (by decide) (by decide) rejected217
theorem rejected218 : ¬ Sat compatible supports domains218 targets218 :=
  refute_split compatible supports domains218 targets218 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected218_5, (List.forall_mem_cons.mpr ⟨child_rejected218_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected218
theorem rejected219 : ¬ Sat compatible supports domains219 targets219 :=
  refute_empty_domain compatible supports domains219 targets219 14 (by decide)
#print axioms rejected219
theorem rejected220 : ¬ Sat compatible supports domains220 targets220 :=
  refute_empty_domain compatible supports domains220 targets220 14 (by decide)
#print axioms rejected220
set_option maxRecDepth 8192 in
theorem child_rejected221_194 : ¬ Sat compatible supports (childDomains compatible supports domains221 targets221 13 194) (childTargets supports targets221 194) :=
  transport_child domains221 targets221 13 194 domains219 targets219 (by decide) (by decide) rejected219
set_option maxRecDepth 8192 in
theorem child_rejected221_197 : ¬ Sat compatible supports (childDomains compatible supports domains221 targets221 13 197) (childTargets supports targets221 197) :=
  transport_child domains221 targets221 13 197 domains220 targets220 (by decide) (by decide) rejected220
theorem rejected221 : ¬ Sat compatible supports domains221 targets221 :=
  refute_split compatible supports domains221 targets221 13 [194, 197] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected221_194, (List.forall_mem_cons.mpr ⟨child_rejected221_197, List.forall_mem_nil _⟩)⟩)
#print axioms rejected221
set_option maxRecDepth 8192 in
theorem child_rejected222_217 : ¬ Sat compatible supports (childDomains compatible supports domains222 targets222 15 217) (childTargets supports targets222 217) :=
  transport_child domains222 targets222 15 217 domains221 targets221 (by decide) (by decide) rejected221
theorem rejected222 : ¬ Sat compatible supports domains222 targets222 :=
  refute_split compatible supports domains222 targets222 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected222_217, List.forall_mem_nil _⟩)
#print axioms rejected222
set_option maxRecDepth 8192 in
theorem child_rejected223_117 : ¬ Sat compatible supports (childDomains compatible supports domains223 targets223 8 117) (childTargets supports targets223 117) :=
  transport_child domains223 targets223 8 117 domains222 targets222 (by decide) (by decide) rejected222
theorem rejected223 : ¬ Sat compatible supports domains223 targets223 :=
  refute_split compatible supports domains223 targets223 8 [117] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected223_117, List.forall_mem_nil _⟩)
#print axioms rejected223
end ElevenSquare.Pending.EncodedSearch
