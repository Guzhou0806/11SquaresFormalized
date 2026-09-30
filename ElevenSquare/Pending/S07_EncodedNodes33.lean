import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes32
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected264 : ¬ Sat compatible supports domains264 targets264 :=
  refute_empty_domain compatible supports domains264 targets264 14 (by decide)
#print axioms rejected264
set_option maxRecDepth 8192 in
theorem child_rejected265_218 : ¬ Sat compatible supports (childDomains compatible supports domains265 targets265 15 218) (childTargets supports targets265 218) :=
  transport_child domains265 targets265 15 218 domains264 targets264 (by decide) (by decide) rejected264
theorem rejected265 : ¬ Sat compatible supports domains265 targets265 :=
  refute_split compatible supports domains265 targets265 15 [218] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected265_218, List.forall_mem_nil _⟩)
#print axioms rejected265
set_option maxRecDepth 8192 in
theorem child_rejected266_173 : ¬ Sat compatible supports (childDomains compatible supports domains266 targets266 11 173) (childTargets supports targets266 173) :=
  transport_child domains266 targets266 11 173 domains263 targets263 (by decide) (by decide) rejected263
set_option maxRecDepth 8192 in
theorem child_rejected266_175 : ¬ Sat compatible supports (childDomains compatible supports domains266 targets266 11 175) (childTargets supports targets266 175) :=
  transport_child domains266 targets266 11 175 domains265 targets265 (by decide) (by decide) rejected265
theorem rejected266 : ¬ Sat compatible supports domains266 targets266 :=
  refute_split compatible supports domains266 targets266 11 [173, 175] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected266_173, (List.forall_mem_cons.mpr ⟨child_rejected266_175, List.forall_mem_nil _⟩)⟩)
#print axioms rejected266
set_option maxRecDepth 8192 in
theorem child_rejected267_79 : ¬ Sat compatible supports (childDomains compatible supports domains267 targets267 6 79) (childTargets supports targets267 79) :=
  transport_child domains267 targets267 6 79 domains266 targets266 (by decide) (by decide) rejected266
theorem rejected267 : ¬ Sat compatible supports domains267 targets267 :=
  refute_split compatible supports domains267 targets267 6 [79] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected267_79, List.forall_mem_nil _⟩)
#print axioms rejected267
set_option maxRecDepth 8192 in
theorem child_rejected268_138 : ¬ Sat compatible supports (childDomains compatible supports domains268 targets268 9 138) (childTargets supports targets268 138) :=
  transport_child domains268 targets268 9 138 domains267 targets267 (by decide) (by decide) rejected267
theorem rejected268 : ¬ Sat compatible supports domains268 targets268 :=
  refute_split compatible supports domains268 targets268 9 [138] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected268_138, List.forall_mem_nil _⟩)
#print axioms rejected268
theorem rejected269 : ¬ Sat compatible supports domains269 targets269 :=
  refute_empty_domain compatible supports domains269 targets269 9 (by decide)
#print axioms rejected269
set_option maxRecDepth 8192 in
theorem child_rejected270_86 : ¬ Sat compatible supports (childDomains compatible supports domains270 targets270 6 86) (childTargets supports targets270 86) :=
  transport_child domains270 targets270 6 86 domains269 targets269 (by decide) (by decide) rejected269
theorem rejected270 : ¬ Sat compatible supports domains270 targets270 :=
  refute_split compatible supports domains270 targets270 6 [86] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected270_86, List.forall_mem_nil _⟩)
#print axioms rejected270
theorem rejected271 : ¬ Sat compatible supports domains271 targets271 :=
  refute_empty_domain compatible supports domains271 targets271 8 (by decide)
#print axioms rejected271
end ElevenSquare.Pending.EncodedSearch
