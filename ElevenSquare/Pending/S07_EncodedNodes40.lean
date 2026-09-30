import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected320 : ¬ Sat compatible supports domains320 targets320 :=
  refute_empty_domain compatible supports domains320 targets320 13 (by decide)
#print axioms rejected320
set_option maxRecDepth 8192 in
theorem child_rejected321_205 : ¬ Sat compatible supports (childDomains compatible supports domains321 targets321 14 205) (childTargets supports targets321 205) :=
  transport_child domains321 targets321 14 205 domains320 targets320 (by decide) (by decide) rejected320
theorem rejected321 : ¬ Sat compatible supports domains321 targets321 :=
  refute_split compatible supports domains321 targets321 14 [205] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected321_205, List.forall_mem_nil _⟩)
#print axioms rejected321
set_option maxRecDepth 8192 in
theorem child_rejected322_217 : ¬ Sat compatible supports (childDomains compatible supports domains322 targets322 15 217) (childTargets supports targets322 217) :=
  transport_child domains322 targets322 15 217 domains321 targets321 (by decide) (by decide) rejected321
theorem rejected322 : ¬ Sat compatible supports domains322 targets322 :=
  refute_split compatible supports domains322 targets322 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected322_217, List.forall_mem_nil _⟩)
#print axioms rejected322
theorem rejected323 : ¬ Sat compatible supports domains323 targets323 :=
  refute_empty_domain compatible supports domains323 targets323 14 (by decide)
#print axioms rejected323
set_option maxRecDepth 8192 in
theorem child_rejected324_196 : ¬ Sat compatible supports (childDomains compatible supports domains324 targets324 13 196) (childTargets supports targets324 196) :=
  transport_child domains324 targets324 13 196 domains323 targets323 (by decide) (by decide) rejected323
theorem rejected324 : ¬ Sat compatible supports domains324 targets324 :=
  refute_split compatible supports domains324 targets324 13 [196] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected324_196, List.forall_mem_nil _⟩)
#print axioms rejected324
set_option maxRecDepth 8192 in
theorem child_rejected325_116 : ¬ Sat compatible supports (childDomains compatible supports domains325 targets325 8 116) (childTargets supports targets325 116) :=
  transport_child domains325 targets325 8 116 domains324 targets324 (by decide) (by decide) rejected324
theorem rejected325 : ¬ Sat compatible supports domains325 targets325 :=
  refute_split compatible supports domains325 targets325 8 [116] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected325_116, List.forall_mem_nil _⟩)
#print axioms rejected325
set_option maxRecDepth 8192 in
theorem child_rejected326_217 : ¬ Sat compatible supports (childDomains compatible supports domains326 targets326 15 217) (childTargets supports targets326 217) :=
  transport_child domains326 targets326 15 217 domains325 targets325 (by decide) (by decide) rejected325
theorem rejected326 : ¬ Sat compatible supports domains326 targets326 :=
  refute_split compatible supports domains326 targets326 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected326_217, List.forall_mem_nil _⟩)
#print axioms rejected326
set_option maxRecDepth 8192 in
theorem child_rejected327_5 : ¬ Sat compatible supports (childDomains compatible supports domains327 targets327 0 5) (childTargets supports targets327 5) :=
  transport_child domains327 targets327 0 5 domains322 targets322 (by decide) (by decide) rejected322
set_option maxRecDepth 8192 in
theorem child_rejected327_8 : ¬ Sat compatible supports (childDomains compatible supports domains327 targets327 0 8) (childTargets supports targets327 8) :=
  transport_child domains327 targets327 0 8 domains326 targets326 (by decide) (by decide) rejected326
theorem rejected327 : ¬ Sat compatible supports domains327 targets327 :=
  refute_split compatible supports domains327 targets327 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected327_5, (List.forall_mem_cons.mpr ⟨child_rejected327_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected327
end ElevenSquare.Pending.EncodedSearch
