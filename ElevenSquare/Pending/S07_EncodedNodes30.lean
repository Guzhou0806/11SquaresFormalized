import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected240 : ¬ Sat compatible supports domains240 targets240 :=
  refute_empty_domain compatible supports domains240 targets240 13 (by decide)
#print axioms rejected240
set_option maxRecDepth 8192 in
theorem child_rejected241_2 : ¬ Sat compatible supports (childDomains compatible supports domains241 targets241 0 2) (childTargets supports targets241 2) :=
  transport_child domains241 targets241 0 2 domains240 targets240 (by decide) (by decide) rejected240
theorem rejected241 : ¬ Sat compatible supports domains241 targets241 :=
  refute_split compatible supports domains241 targets241 0 [2] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected241_2, List.forall_mem_nil _⟩)
#print axioms rejected241
theorem rejected242 : ¬ Sat compatible supports domains242 targets242 :=
  refute_empty_domain compatible supports domains242 targets242 13 (by decide)
#print axioms rejected242
theorem rejected243 : ¬ Sat compatible supports domains243 targets243 :=
  refute_empty_domain compatible supports domains243 targets243 8 (by decide)
#print axioms rejected243
theorem rejected244 : ¬ Sat compatible supports domains244 targets244 :=
  refute_empty_domain compatible supports domains244 targets244 0 (by decide)
#print axioms rejected244
set_option maxRecDepth 8192 in
theorem child_rejected245_116 : ¬ Sat compatible supports (childDomains compatible supports domains245 targets245 8 116) (childTargets supports targets245 116) :=
  transport_child domains245 targets245 8 116 domains244 targets244 (by decide) (by decide) rejected244
theorem rejected245 : ¬ Sat compatible supports domains245 targets245 :=
  refute_split compatible supports domains245 targets245 8 [116] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected245_116, List.forall_mem_nil _⟩)
#print axioms rejected245
set_option maxRecDepth 8192 in
theorem child_rejected246_186 : ¬ Sat compatible supports (childDomains compatible supports domains246 targets246 13 186) (childTargets supports targets246 186) :=
  transport_child domains246 targets246 13 186 domains243 targets243 (by decide) (by decide) rejected243
set_option maxRecDepth 8192 in
theorem child_rejected246_198 : ¬ Sat compatible supports (childDomains compatible supports domains246 targets246 13 198) (childTargets supports targets246 198) :=
  transport_child domains246 targets246 13 198 domains245 targets245 (by decide) (by decide) rejected245
theorem rejected246 : ¬ Sat compatible supports domains246 targets246 :=
  refute_split compatible supports domains246 targets246 13 [186, 198] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected246_186, (List.forall_mem_cons.mpr ⟨child_rejected246_198, List.forall_mem_nil _⟩)⟩)
#print axioms rejected246
set_option maxRecDepth 8192 in
theorem child_rejected247_202 : ¬ Sat compatible supports (childDomains compatible supports domains247 targets247 14 202) (childTargets supports targets247 202) :=
  transport_child domains247 targets247 14 202 domains241 targets241 (by decide) (by decide) rejected241
set_option maxRecDepth 8192 in
theorem child_rejected247_205 : ¬ Sat compatible supports (childDomains compatible supports domains247 targets247 14 205) (childTargets supports targets247 205) :=
  transport_child domains247 targets247 14 205 domains242 targets242 (by decide) (by decide) rejected242
set_option maxRecDepth 8192 in
theorem child_rejected247_206 : ¬ Sat compatible supports (childDomains compatible supports domains247 targets247 14 206) (childTargets supports targets247 206) :=
  transport_child domains247 targets247 14 206 domains246 targets246 (by decide) (by decide) rejected246
theorem rejected247 : ¬ Sat compatible supports domains247 targets247 :=
  refute_split compatible supports domains247 targets247 14 [202, 205, 206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected247_202, (List.forall_mem_cons.mpr ⟨child_rejected247_205, (List.forall_mem_cons.mpr ⟨child_rejected247_206, List.forall_mem_nil _⟩)⟩)⟩)
#print axioms rejected247
end ElevenSquare.Pending.EncodedSearch
