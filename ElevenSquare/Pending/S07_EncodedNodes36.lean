import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected288 : ¬ Sat compatible supports domains288 targets288 :=
  refute_empty_domain compatible supports domains288 targets288 14 (by decide)
#print axioms rejected288
theorem rejected289 : ¬ Sat compatible supports domains289 targets289 :=
  refute_empty_domain compatible supports domains289 targets289 14 (by decide)
#print axioms rejected289
set_option maxRecDepth 8192 in
theorem child_rejected290_194 : ¬ Sat compatible supports (childDomains compatible supports domains290 targets290 13 194) (childTargets supports targets290 194) :=
  transport_child domains290 targets290 13 194 domains288 targets288 (by decide) (by decide) rejected288
set_option maxRecDepth 8192 in
theorem child_rejected290_197 : ¬ Sat compatible supports (childDomains compatible supports domains290 targets290 13 197) (childTargets supports targets290 197) :=
  transport_child domains290 targets290 13 197 domains289 targets289 (by decide) (by decide) rejected289
theorem rejected290 : ¬ Sat compatible supports domains290 targets290 :=
  refute_split compatible supports domains290 targets290 13 [194, 197] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected290_194, (List.forall_mem_cons.mpr ⟨child_rejected290_197, List.forall_mem_nil _⟩)⟩)
#print axioms rejected290
theorem rejected291 : ¬ Sat compatible supports domains291 targets291 :=
  refute_empty_domain compatible supports domains291 targets291 5 (by decide)
#print axioms rejected291
theorem rejected292 : ¬ Sat compatible supports domains292 targets292 :=
  refute_empty_domain compatible supports domains292 targets292 5 (by decide)
#print axioms rejected292
theorem rejected293 : ¬ Sat compatible supports domains293 targets293 :=
  refute_empty_domain compatible supports domains293 targets293 5 (by decide)
#print axioms rejected293
theorem rejected294 : ¬ Sat compatible supports domains294 targets294 :=
  refute_empty_domain compatible supports domains294 targets294 15 (by decide)
#print axioms rejected294
theorem rejected295 : ¬ Sat compatible supports domains295 targets295 :=
  refute_empty_domain compatible supports domains295 targets295 14 (by decide)
#print axioms rejected295
end ElevenSquare.Pending.EncodedSearch
