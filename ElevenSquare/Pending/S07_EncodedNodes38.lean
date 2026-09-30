import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected304 : ¬ Sat compatible supports domains304 targets304 :=
  refute_empty_domain compatible supports domains304 targets304 9 (by decide)
#print axioms rejected304
theorem rejected305 : ¬ Sat compatible supports domains305 targets305 :=
  refute_empty_domain compatible supports domains305 targets305 6 (by decide)
#print axioms rejected305
theorem rejected306 : ¬ Sat compatible supports domains306 targets306 :=
  refute_empty_domain compatible supports domains306 targets306 13 (by decide)
#print axioms rejected306
set_option maxRecDepth 8192 in
theorem child_rejected307_205 : ¬ Sat compatible supports (childDomains compatible supports domains307 targets307 14 205) (childTargets supports targets307 205) :=
  transport_child domains307 targets307 14 205 domains306 targets306 (by decide) (by decide) rejected306
theorem rejected307 : ¬ Sat compatible supports domains307 targets307 :=
  refute_split compatible supports domains307 targets307 14 [205] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected307_205, List.forall_mem_nil _⟩)
#print axioms rejected307
set_option maxRecDepth 8192 in
theorem child_rejected308_138 : ¬ Sat compatible supports (childDomains compatible supports domains308 targets308 9 138) (childTargets supports targets308 138) :=
  transport_child domains308 targets308 9 138 domains305 targets305 (by decide) (by decide) rejected305
set_option maxRecDepth 8192 in
theorem child_rejected308_142 : ¬ Sat compatible supports (childDomains compatible supports domains308 targets308 9 142) (childTargets supports targets308 142) :=
  transport_child domains308 targets308 9 142 domains307 targets307 (by decide) (by decide) rejected307
theorem rejected308 : ¬ Sat compatible supports domains308 targets308 :=
  refute_split compatible supports domains308 targets308 9 [138, 142] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected308_138, (List.forall_mem_cons.mpr ⟨child_rejected308_142, List.forall_mem_nil _⟩)⟩)
#print axioms rejected308
set_option maxRecDepth 8192 in
theorem child_rejected309_65 : ¬ Sat compatible supports (childDomains compatible supports domains309 targets309 5 65) (childTargets supports targets309 65) :=
  transport_child domains309 targets309 5 65 domains304 targets304 (by decide) (by decide) rejected304
set_option maxRecDepth 8192 in
theorem child_rejected309_70 : ¬ Sat compatible supports (childDomains compatible supports domains309 targets309 5 70) (childTargets supports targets309 70) :=
  transport_child domains309 targets309 5 70 domains308 targets308 (by decide) (by decide) rejected308
theorem rejected309 : ¬ Sat compatible supports domains309 targets309 :=
  refute_split compatible supports domains309 targets309 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected309_65, (List.forall_mem_cons.mpr ⟨child_rejected309_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected309
set_option maxRecDepth 8192 in
theorem child_rejected310_217 : ¬ Sat compatible supports (childDomains compatible supports domains310 targets310 15 217) (childTargets supports targets310 217) :=
  transport_child domains310 targets310 15 217 domains309 targets309 (by decide) (by decide) rejected309
theorem rejected310 : ¬ Sat compatible supports domains310 targets310 :=
  refute_split compatible supports domains310 targets310 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected310_217, List.forall_mem_nil _⟩)
#print axioms rejected310
theorem rejected311 : ¬ Sat compatible supports domains311 targets311 :=
  refute_empty_domain compatible supports domains311 targets311 6 (by decide)
#print axioms rejected311
end ElevenSquare.Pending.EncodedSearch
