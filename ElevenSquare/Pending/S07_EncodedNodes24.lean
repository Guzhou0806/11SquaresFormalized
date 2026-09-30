import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes23
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected192_70 : ¬ Sat compatible supports (childDomains compatible supports domains192 targets192 5 70) (childTargets supports targets192 70) :=
  transport_child domains192 targets192 5 70 domains191 targets191 (by decide) (by decide) rejected191
theorem rejected192 : ¬ Sat compatible supports domains192 targets192 :=
  refute_split compatible supports domains192 targets192 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected192_70, List.forall_mem_nil _⟩)
#print axioms rejected192
set_option maxRecDepth 8192 in
theorem child_rejected193_5 : ¬ Sat compatible supports (childDomains compatible supports domains193 targets193 0 5) (childTargets supports targets193 5) :=
  transport_child domains193 targets193 0 5 domains189 targets189 (by decide) (by decide) rejected189
set_option maxRecDepth 8192 in
theorem child_rejected193_8 : ¬ Sat compatible supports (childDomains compatible supports domains193 targets193 0 8) (childTargets supports targets193 8) :=
  transport_child domains193 targets193 0 8 domains192 targets192 (by decide) (by decide) rejected192
theorem rejected193 : ¬ Sat compatible supports domains193 targets193 :=
  refute_split compatible supports domains193 targets193 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected193_5, (List.forall_mem_cons.mpr ⟨child_rejected193_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected193
theorem rejected194 : ¬ Sat compatible supports domains194 targets194 :=
  refute_empty_domain compatible supports domains194 targets194 13 (by decide)
#print axioms rejected194
theorem rejected195 : ¬ Sat compatible supports domains195 targets195 :=
  refute_empty_domain compatible supports domains195 targets195 13 (by decide)
#print axioms rejected195
set_option maxRecDepth 8192 in
theorem child_rejected196_202 : ¬ Sat compatible supports (childDomains compatible supports domains196 targets196 14 202) (childTargets supports targets196 202) :=
  transport_child domains196 targets196 14 202 domains194 targets194 (by decide) (by decide) rejected194
set_option maxRecDepth 8192 in
theorem child_rejected196_206 : ¬ Sat compatible supports (childDomains compatible supports domains196 targets196 14 206) (childTargets supports targets196 206) :=
  transport_child domains196 targets196 14 206 domains195 targets195 (by decide) (by decide) rejected195
theorem rejected196 : ¬ Sat compatible supports domains196 targets196 :=
  refute_split compatible supports domains196 targets196 14 [202, 206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected196_202, (List.forall_mem_cons.mpr ⟨child_rejected196_206, List.forall_mem_nil _⟩)⟩)
#print axioms rejected196
theorem rejected197 : ¬ Sat compatible supports domains197 targets197 :=
  refute_empty_domain compatible supports domains197 targets197 14 (by decide)
#print axioms rejected197
theorem rejected198 : ¬ Sat compatible supports domains198 targets198 :=
  refute_empty_domain compatible supports domains198 targets198 14 (by decide)
#print axioms rejected198
set_option maxRecDepth 8192 in
theorem child_rejected199_194 : ¬ Sat compatible supports (childDomains compatible supports domains199 targets199 13 194) (childTargets supports targets199 194) :=
  transport_child domains199 targets199 13 194 domains197 targets197 (by decide) (by decide) rejected197
set_option maxRecDepth 8192 in
theorem child_rejected199_197 : ¬ Sat compatible supports (childDomains compatible supports domains199 targets199 13 197) (childTargets supports targets199 197) :=
  transport_child domains199 targets199 13 197 domains198 targets198 (by decide) (by decide) rejected198
theorem rejected199 : ¬ Sat compatible supports domains199 targets199 :=
  refute_split compatible supports domains199 targets199 13 [194, 197] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected199_194, (List.forall_mem_cons.mpr ⟨child_rejected199_197, List.forall_mem_nil _⟩)⟩)
#print axioms rejected199
end ElevenSquare.Pending.EncodedSearch
