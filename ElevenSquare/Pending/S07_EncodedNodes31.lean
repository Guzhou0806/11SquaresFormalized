import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected248 : ¬ Sat compatible supports domains248 targets248 :=
  refute_empty_domain compatible supports domains248 targets248 15 (by decide)
#print axioms rejected248
theorem rejected249 : ¬ Sat compatible supports domains249 targets249 :=
  refute_empty_domain compatible supports domains249 targets249 15 (by decide)
#print axioms rejected249
set_option maxRecDepth 8192 in
theorem child_rejected250_201 : ¬ Sat compatible supports (childDomains compatible supports domains250 targets250 14 201) (childTargets supports targets250 201) :=
  transport_child domains250 targets250 14 201 domains248 targets248 (by decide) (by decide) rejected248
set_option maxRecDepth 8192 in
theorem child_rejected250_204 : ¬ Sat compatible supports (childDomains compatible supports domains250 targets250 14 204) (childTargets supports targets250 204) :=
  transport_child domains250 targets250 14 204 domains249 targets249 (by decide) (by decide) rejected249
theorem rejected250 : ¬ Sat compatible supports domains250 targets250 :=
  refute_split compatible supports domains250 targets250 14 [201, 204] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected250_201, (List.forall_mem_cons.mpr ⟨child_rejected250_204, List.forall_mem_nil _⟩)⟩)
#print axioms rejected250
theorem rejected251 : ¬ Sat compatible supports domains251 targets251 :=
  refute_empty_domain compatible supports domains251 targets251 15 (by decide)
#print axioms rejected251
set_option maxRecDepth 8192 in
theorem child_rejected252_204 : ¬ Sat compatible supports (childDomains compatible supports domains252 targets252 14 204) (childTargets supports targets252 204) :=
  transport_child domains252 targets252 14 204 domains251 targets251 (by decide) (by decide) rejected251
theorem rejected252 : ¬ Sat compatible supports domains252 targets252 :=
  refute_split compatible supports domains252 targets252 14 [204] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected252_204, List.forall_mem_nil _⟩)
#print axioms rejected252
set_option maxRecDepth 8192 in
theorem child_rejected253_195 : ¬ Sat compatible supports (childDomains compatible supports domains253 targets253 13 195) (childTargets supports targets253 195) :=
  transport_child domains253 targets253 13 195 domains250 targets250 (by decide) (by decide) rejected250
set_option maxRecDepth 8192 in
theorem child_rejected253_198 : ¬ Sat compatible supports (childDomains compatible supports domains253 targets253 13 198) (childTargets supports targets253 198) :=
  transport_child domains253 targets253 13 198 domains252 targets252 (by decide) (by decide) rejected252
theorem rejected253 : ¬ Sat compatible supports domains253 targets253 :=
  refute_split compatible supports domains253 targets253 13 [195, 198] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected253_195, (List.forall_mem_cons.mpr ⟨child_rejected253_198, List.forall_mem_nil _⟩)⟩)
#print axioms rejected253
theorem rejected254 : ¬ Sat compatible supports domains254 targets254 :=
  refute_empty_domain compatible supports domains254 targets254 15 (by decide)
#print axioms rejected254
theorem rejected255 : ¬ Sat compatible supports domains255 targets255 :=
  refute_empty_domain compatible supports domains255 targets255 15 (by decide)
#print axioms rejected255
end ElevenSquare.Pending.EncodedSearch
