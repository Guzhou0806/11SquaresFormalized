import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes30
import ElevenSquare.Pending.S07_EncodedNodes35
import ElevenSquare.Pending.S07_EncodedNodes37
import ElevenSquare.Pending.S07_EncodedNodes38
import ElevenSquare.Pending.S07_EncodedNodes39
import ElevenSquare.Pending.S07_EncodedNodes40
import ElevenSquare.Pending.S07_EncodedNodes41
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected336_5 : ¬ Sat compatible supports (childDomains compatible supports domains336 targets336 0 5) (childTargets supports targets336 5) :=
  transport_child domains336 targets336 0 5 domains331 targets331 (by decide) (by decide) rejected331
set_option maxRecDepth 8192 in
theorem child_rejected336_8 : ¬ Sat compatible supports (childDomains compatible supports domains336 targets336 0 8) (childTargets supports targets336 8) :=
  transport_child domains336 targets336 0 8 domains335 targets335 (by decide) (by decide) rejected335
theorem rejected336 : ¬ Sat compatible supports domains336 targets336 :=
  refute_split compatible supports domains336 targets336 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected336_5, (List.forall_mem_cons.mpr ⟨child_rejected336_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected336
set_option maxRecDepth 8192 in
theorem child_rejected337_12 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 12) (childTargets supports targets337 12) :=
  transport_child domains337 targets337 1 12 domains247 targets247 (by decide) (by decide) rejected247
set_option maxRecDepth 8192 in
theorem child_rejected337_13 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 13) (childTargets supports targets337 13) :=
  transport_child domains337 targets337 1 13 domains287 targets287 (by decide) (by decide) rejected287
set_option maxRecDepth 8192 in
theorem child_rejected337_14 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 14) (childTargets supports targets337 14) :=
  transport_child domains337 targets337 1 14 domains300 targets300 (by decide) (by decide) rejected300
set_option maxRecDepth 8192 in
theorem child_rejected337_15 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 15) (childTargets supports targets337 15) :=
  transport_child domains337 targets337 1 15 domains303 targets303 (by decide) (by decide) rejected303
set_option maxRecDepth 8192 in
theorem child_rejected337_16 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 16) (childTargets supports targets337 16) :=
  transport_child domains337 targets337 1 16 domains310 targets310 (by decide) (by decide) rejected310
set_option maxRecDepth 8192 in
theorem child_rejected337_17 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 17) (childTargets supports targets337 17) :=
  transport_child domains337 targets337 1 17 domains319 targets319 (by decide) (by decide) rejected319
set_option maxRecDepth 8192 in
theorem child_rejected337_18 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 18) (childTargets supports targets337 18) :=
  transport_child domains337 targets337 1 18 domains327 targets327 (by decide) (by decide) rejected327
set_option maxRecDepth 8192 in
theorem child_rejected337_19 : ¬ Sat compatible supports (childDomains compatible supports domains337 targets337 1 19) (childTargets supports targets337 19) :=
  transport_child domains337 targets337 1 19 domains336 targets336 (by decide) (by decide) rejected336
theorem rejected337 : ¬ Sat compatible supports domains337 targets337 :=
  refute_split compatible supports domains337 targets337 1 [12, 13, 14, 15, 16, 17, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected337_12, (List.forall_mem_cons.mpr ⟨child_rejected337_13, (List.forall_mem_cons.mpr ⟨child_rejected337_14, (List.forall_mem_cons.mpr ⟨child_rejected337_15, (List.forall_mem_cons.mpr ⟨child_rejected337_16, (List.forall_mem_cons.mpr ⟨child_rejected337_17, (List.forall_mem_cons.mpr ⟨child_rejected337_18, (List.forall_mem_cons.mpr ⟨child_rejected337_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected337
theorem rejected338 : ¬ Sat compatible supports domains338 targets338 :=
  refute_empty_domain compatible supports domains338 targets338 9 (by decide)
#print axioms rejected338
set_option maxRecDepth 8192 in
theorem child_rejected339_191 : ¬ Sat compatible supports (childDomains compatible supports domains339 targets339 13 191) (childTargets supports targets339 191) :=
  transport_child domains339 targets339 13 191 domains338 targets338 (by decide) (by decide) rejected338
theorem rejected339 : ¬ Sat compatible supports domains339 targets339 :=
  refute_split compatible supports domains339 targets339 13 [191] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected339_191, List.forall_mem_nil _⟩)
#print axioms rejected339
set_option maxRecDepth 8192 in
theorem child_rejected340_206 : ¬ Sat compatible supports (childDomains compatible supports domains340 targets340 14 206) (childTargets supports targets340 206) :=
  transport_child domains340 targets340 14 206 domains339 targets339 (by decide) (by decide) rejected339
theorem rejected340 : ¬ Sat compatible supports domains340 targets340 :=
  refute_split compatible supports domains340 targets340 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected340_206, List.forall_mem_nil _⟩)
#print axioms rejected340
theorem rejected341 : ¬ Sat compatible supports domains341 targets341 :=
  refute_empty_domain compatible supports domains341 targets341 9 (by decide)
#print axioms rejected341
set_option maxRecDepth 8192 in
theorem child_rejected342_191 : ¬ Sat compatible supports (childDomains compatible supports domains342 targets342 13 191) (childTargets supports targets342 191) :=
  transport_child domains342 targets342 13 191 domains341 targets341 (by decide) (by decide) rejected341
theorem rejected342 : ¬ Sat compatible supports domains342 targets342 :=
  refute_split compatible supports domains342 targets342 13 [191] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected342_191, List.forall_mem_nil _⟩)
#print axioms rejected342
set_option maxRecDepth 8192 in
theorem child_rejected343_206 : ¬ Sat compatible supports (childDomains compatible supports domains343 targets343 14 206) (childTargets supports targets343 206) :=
  transport_child domains343 targets343 14 206 domains342 targets342 (by decide) (by decide) rejected342
theorem rejected343 : ¬ Sat compatible supports domains343 targets343 :=
  refute_split compatible supports domains343 targets343 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected343_206, List.forall_mem_nil _⟩)
#print axioms rejected343
end ElevenSquare.Pending.EncodedSearch
