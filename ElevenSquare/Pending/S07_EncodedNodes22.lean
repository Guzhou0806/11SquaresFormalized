import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes14
import ElevenSquare.Pending.S07_EncodedNodes18
import ElevenSquare.Pending.S07_EncodedNodes20
import ElevenSquare.Pending.S07_EncodedNodes21
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected176 : ¬ Sat compatible supports domains176 targets176 :=
  refute_empty_domain compatible supports domains176 targets176 1 (by decide)
#print axioms rejected176
set_option maxRecDepth 8192 in
theorem child_rejected177_3 : ¬ Sat compatible supports (childDomains compatible supports domains177 targets177 0 3) (childTargets supports targets177 3) :=
  transport_child domains177 targets177 0 3 domains176 targets176 (by decide) (by decide) rejected176
theorem rejected177 : ¬ Sat compatible supports domains177 targets177 :=
  refute_split compatible supports domains177 targets177 0 [3] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected177_3, List.forall_mem_nil _⟩)
#print axioms rejected177
set_option maxRecDepth 8192 in
theorem child_rejected178_184 : ¬ Sat compatible supports (childDomains compatible supports domains178 targets178 12 184) (childTargets supports targets178 184) :=
  transport_child domains178 targets178 12 184 domains177 targets177 (by decide) (by decide) rejected177
theorem rejected178 : ¬ Sat compatible supports domains178 targets178 :=
  refute_split compatible supports domains178 targets178 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected178_184, List.forall_mem_nil _⟩)
#print axioms rejected178
theorem rejected179 : ¬ Sat compatible supports domains179 targets179 :=
  refute_empty_domain compatible supports domains179 targets179 1 (by decide)
#print axioms rejected179
theorem rejected180 : ¬ Sat compatible supports domains180 targets180 :=
  refute_empty_domain compatible supports domains180 targets180 1 (by decide)
#print axioms rejected180
set_option maxRecDepth 8192 in
theorem child_rejected181_2 : ¬ Sat compatible supports (childDomains compatible supports domains181 targets181 0 2) (childTargets supports targets181 2) :=
  transport_child domains181 targets181 0 2 domains179 targets179 (by decide) (by decide) rejected179
set_option maxRecDepth 8192 in
theorem child_rejected181_3 : ¬ Sat compatible supports (childDomains compatible supports domains181 targets181 0 3) (childTargets supports targets181 3) :=
  transport_child domains181 targets181 0 3 domains180 targets180 (by decide) (by decide) rejected180
theorem rejected181 : ¬ Sat compatible supports domains181 targets181 :=
  refute_split compatible supports domains181 targets181 0 [2, 3] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected181_2, (List.forall_mem_cons.mpr ⟨child_rejected181_3, List.forall_mem_nil _⟩)⟩)
#print axioms rejected181
set_option maxRecDepth 8192 in
theorem child_rejected182_184 : ¬ Sat compatible supports (childDomains compatible supports domains182 targets182 12 184) (childTargets supports targets182 184) :=
  transport_child domains182 targets182 12 184 domains181 targets181 (by decide) (by decide) rejected181
theorem rejected182 : ¬ Sat compatible supports domains182 targets182 :=
  refute_split compatible supports domains182 targets182 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected182_184, List.forall_mem_nil _⟩)
#print axioms rejected182
set_option maxRecDepth 8192 in
theorem child_rejected183_34 : ¬ Sat compatible supports (childDomains compatible supports domains183 targets183 3 34) (childTargets supports targets183 34) :=
  transport_child domains183 targets183 3 34 domains116 targets116 (by decide) (by decide) rejected116
set_option maxRecDepth 8192 in
theorem child_rejected183_35 : ¬ Sat compatible supports (childDomains compatible supports domains183 targets183 3 35) (childTargets supports targets183 35) :=
  transport_child domains183 targets183 3 35 domains150 targets150 (by decide) (by decide) rejected150
set_option maxRecDepth 8192 in
theorem child_rejected183_36 : ¬ Sat compatible supports (childDomains compatible supports domains183 targets183 3 36) (childTargets supports targets183 36) :=
  transport_child domains183 targets183 3 36 domains164 targets164 (by decide) (by decide) rejected164
set_option maxRecDepth 8192 in
theorem child_rejected183_37 : ¬ Sat compatible supports (childDomains compatible supports domains183 targets183 3 37) (childTargets supports targets183 37) :=
  transport_child domains183 targets183 3 37 domains175 targets175 (by decide) (by decide) rejected175
set_option maxRecDepth 8192 in
theorem child_rejected183_38 : ¬ Sat compatible supports (childDomains compatible supports domains183 targets183 3 38) (childTargets supports targets183 38) :=
  transport_child domains183 targets183 3 38 domains178 targets178 (by decide) (by decide) rejected178
set_option maxRecDepth 8192 in
theorem child_rejected183_39 : ¬ Sat compatible supports (childDomains compatible supports domains183 targets183 3 39) (childTargets supports targets183 39) :=
  transport_child domains183 targets183 3 39 domains182 targets182 (by decide) (by decide) rejected182
theorem rejected183 : ¬ Sat compatible supports domains183 targets183 :=
  refute_split compatible supports domains183 targets183 3 [34, 35, 36, 37, 38, 39] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected183_34, (List.forall_mem_cons.mpr ⟨child_rejected183_35, (List.forall_mem_cons.mpr ⟨child_rejected183_36, (List.forall_mem_cons.mpr ⟨child_rejected183_37, (List.forall_mem_cons.mpr ⟨child_rejected183_38, (List.forall_mem_cons.mpr ⟨child_rejected183_39, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected183
end ElevenSquare.Pending.EncodedSearch
