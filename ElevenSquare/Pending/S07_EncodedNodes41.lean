import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected328 : ¬ Sat compatible supports domains328 targets328 :=
  refute_empty_domain compatible supports domains328 targets328 9 (by decide)
#print axioms rejected328
theorem rejected329 : ¬ Sat compatible supports domains329 targets329 :=
  refute_empty_domain compatible supports domains329 targets329 9 (by decide)
#print axioms rejected329
set_option maxRecDepth 8192 in
theorem child_rejected330_65 : ¬ Sat compatible supports (childDomains compatible supports domains330 targets330 5 65) (childTargets supports targets330 65) :=
  transport_child domains330 targets330 5 65 domains328 targets328 (by decide) (by decide) rejected328
set_option maxRecDepth 8192 in
theorem child_rejected330_70 : ¬ Sat compatible supports (childDomains compatible supports domains330 targets330 5 70) (childTargets supports targets330 70) :=
  transport_child domains330 targets330 5 70 domains329 targets329 (by decide) (by decide) rejected329
theorem rejected330 : ¬ Sat compatible supports domains330 targets330 :=
  refute_split compatible supports domains330 targets330 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected330_65, (List.forall_mem_cons.mpr ⟨child_rejected330_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected330
set_option maxRecDepth 8192 in
theorem child_rejected331_217 : ¬ Sat compatible supports (childDomains compatible supports domains331 targets331 15 217) (childTargets supports targets331 217) :=
  transport_child domains331 targets331 15 217 domains330 targets330 (by decide) (by decide) rejected330
theorem rejected331 : ¬ Sat compatible supports domains331 targets331 :=
  refute_split compatible supports domains331 targets331 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected331_217, List.forall_mem_nil _⟩)
#print axioms rejected331
theorem rejected332 : ¬ Sat compatible supports domains332 targets332 :=
  refute_empty_domain compatible supports domains332 targets332 9 (by decide)
#print axioms rejected332
theorem rejected333 : ¬ Sat compatible supports domains333 targets333 :=
  refute_empty_domain compatible supports domains333 targets333 9 (by decide)
#print axioms rejected333
set_option maxRecDepth 8192 in
theorem child_rejected334_65 : ¬ Sat compatible supports (childDomains compatible supports domains334 targets334 5 65) (childTargets supports targets334 65) :=
  transport_child domains334 targets334 5 65 domains332 targets332 (by decide) (by decide) rejected332
set_option maxRecDepth 8192 in
theorem child_rejected334_70 : ¬ Sat compatible supports (childDomains compatible supports domains334 targets334 5 70) (childTargets supports targets334 70) :=
  transport_child domains334 targets334 5 70 domains333 targets333 (by decide) (by decide) rejected333
theorem rejected334 : ¬ Sat compatible supports domains334 targets334 :=
  refute_split compatible supports domains334 targets334 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected334_65, (List.forall_mem_cons.mpr ⟨child_rejected334_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected334
set_option maxRecDepth 8192 in
theorem child_rejected335_217 : ¬ Sat compatible supports (childDomains compatible supports domains335 targets335 15 217) (childTargets supports targets335 217) :=
  transport_child domains335 targets335 15 217 domains334 targets334 (by decide) (by decide) rejected334
theorem rejected335 : ¬ Sat compatible supports domains335 targets335 :=
  refute_split compatible supports domains335 targets335 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected335_217, List.forall_mem_nil _⟩)
#print axioms rejected335
end ElevenSquare.Pending.EncodedSearch
