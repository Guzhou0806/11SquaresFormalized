import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes18
import ElevenSquare.Pending.S07_EncodedNodes19
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected160_92 : ¬ Sat compatible supports (childDomains compatible supports domains160 targets160 6 92) (childTargets supports targets160 92) :=
  transport_child domains160 targets160 6 92 domains159 targets159 (by decide) (by decide) rejected159
theorem rejected160 : ¬ Sat compatible supports domains160 targets160 :=
  refute_split compatible supports domains160 targets160 6 [92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected160_92, List.forall_mem_nil _⟩)
#print axioms rejected160
set_option maxRecDepth 8192 in
theorem child_rejected161_70 : ¬ Sat compatible supports (childDomains compatible supports domains161 targets161 5 70) (childTargets supports targets161 70) :=
  transport_child domains161 targets161 5 70 domains160 targets160 (by decide) (by decide) rejected160
theorem rejected161 : ¬ Sat compatible supports domains161 targets161 :=
  refute_split compatible supports domains161 targets161 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected161_70, List.forall_mem_nil _⟩)
#print axioms rejected161
set_option maxRecDepth 8192 in
theorem child_rejected162_5 : ¬ Sat compatible supports (childDomains compatible supports domains162 targets162 0 5) (childTargets supports targets162 5) :=
  transport_child domains162 targets162 0 5 domains158 targets158 (by decide) (by decide) rejected158
set_option maxRecDepth 8192 in
theorem child_rejected162_8 : ¬ Sat compatible supports (childDomains compatible supports domains162 targets162 0 8) (childTargets supports targets162 8) :=
  transport_child domains162 targets162 0 8 domains161 targets161 (by decide) (by decide) rejected161
theorem rejected162 : ¬ Sat compatible supports domains162 targets162 :=
  refute_split compatible supports domains162 targets162 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected162_5, (List.forall_mem_cons.mpr ⟨child_rejected162_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected162
set_option maxRecDepth 8192 in
theorem child_rejected163_15 : ¬ Sat compatible supports (childDomains compatible supports domains163 targets163 1 15) (childTargets supports targets163 15) :=
  transport_child domains163 targets163 1 15 domains151 targets151 (by decide) (by decide) rejected151
set_option maxRecDepth 8192 in
theorem child_rejected163_16 : ¬ Sat compatible supports (childDomains compatible supports domains163 targets163 1 16) (childTargets supports targets163 16) :=
  transport_child domains163 targets163 1 16 domains154 targets154 (by decide) (by decide) rejected154
set_option maxRecDepth 8192 in
theorem child_rejected163_18 : ¬ Sat compatible supports (childDomains compatible supports domains163 targets163 1 18) (childTargets supports targets163 18) :=
  transport_child domains163 targets163 1 18 domains155 targets155 (by decide) (by decide) rejected155
set_option maxRecDepth 8192 in
theorem child_rejected163_19 : ¬ Sat compatible supports (childDomains compatible supports domains163 targets163 1 19) (childTargets supports targets163 19) :=
  transport_child domains163 targets163 1 19 domains162 targets162 (by decide) (by decide) rejected162
theorem rejected163 : ¬ Sat compatible supports domains163 targets163 :=
  refute_split compatible supports domains163 targets163 1 [15, 16, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected163_15, (List.forall_mem_cons.mpr ⟨child_rejected163_16, (List.forall_mem_cons.mpr ⟨child_rejected163_18, (List.forall_mem_cons.mpr ⟨child_rejected163_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected163
set_option maxRecDepth 8192 in
theorem child_rejected164_184 : ¬ Sat compatible supports (childDomains compatible supports domains164 targets164 12 184) (childTargets supports targets164 184) :=
  transport_child domains164 targets164 12 184 domains163 targets163 (by decide) (by decide) rejected163
theorem rejected164 : ¬ Sat compatible supports domains164 targets164 :=
  refute_split compatible supports domains164 targets164 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected164_184, List.forall_mem_nil _⟩)
#print axioms rejected164
theorem rejected165 : ¬ Sat compatible supports domains165 targets165 :=
  refute_empty_domain compatible supports domains165 targets165 13 (by decide)
#print axioms rejected165
theorem rejected166 : ¬ Sat compatible supports domains166 targets166 :=
  refute_empty_domain compatible supports domains166 targets166 1 (by decide)
#print axioms rejected166
theorem rejected167 : ¬ Sat compatible supports domains167 targets167 :=
  refute_empty_domain compatible supports domains167 targets167 1 (by decide)
#print axioms rejected167
end ElevenSquare.Pending.EncodedSearch
