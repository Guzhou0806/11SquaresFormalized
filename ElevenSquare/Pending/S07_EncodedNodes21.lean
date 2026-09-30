import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes20
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected168 : ¬ Sat compatible supports domains168 targets168 :=
  refute_empty_domain compatible supports domains168 targets168 1 (by decide)
#print axioms rejected168
theorem rejected169 : ¬ Sat compatible supports domains169 targets169 :=
  refute_empty_domain compatible supports domains169 targets169 1 (by decide)
#print axioms rejected169
set_option maxRecDepth 8192 in
theorem child_rejected170_0 : ¬ Sat compatible supports (childDomains compatible supports domains170 targets170 0 0) (childTargets supports targets170 0) :=
  transport_child domains170 targets170 0 0 domains166 targets166 (by decide) (by decide) rejected166
set_option maxRecDepth 8192 in
theorem child_rejected170_1 : ¬ Sat compatible supports (childDomains compatible supports domains170 targets170 0 1) (childTargets supports targets170 1) :=
  transport_child domains170 targets170 0 1 domains167 targets167 (by decide) (by decide) rejected167
set_option maxRecDepth 8192 in
theorem child_rejected170_2 : ¬ Sat compatible supports (childDomains compatible supports domains170 targets170 0 2) (childTargets supports targets170 2) :=
  transport_child domains170 targets170 0 2 domains168 targets168 (by decide) (by decide) rejected168
set_option maxRecDepth 8192 in
theorem child_rejected170_3 : ¬ Sat compatible supports (childDomains compatible supports domains170 targets170 0 3) (childTargets supports targets170 3) :=
  transport_child domains170 targets170 0 3 domains169 targets169 (by decide) (by decide) rejected169
theorem rejected170 : ¬ Sat compatible supports domains170 targets170 :=
  refute_split compatible supports domains170 targets170 0 [0, 1, 2, 3] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected170_0, (List.forall_mem_cons.mpr ⟨child_rejected170_1, (List.forall_mem_cons.mpr ⟨child_rejected170_2, (List.forall_mem_cons.mpr ⟨child_rejected170_3, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected170
theorem rejected171 : ¬ Sat compatible supports domains171 targets171 :=
  refute_empty_domain compatible supports domains171 targets171 1 (by decide)
#print axioms rejected171
set_option maxRecDepth 8192 in
theorem child_rejected172_1 : ¬ Sat compatible supports (childDomains compatible supports domains172 targets172 0 1) (childTargets supports targets172 1) :=
  transport_child domains172 targets172 0 1 domains171 targets171 (by decide) (by decide) rejected171
theorem rejected172 : ¬ Sat compatible supports domains172 targets172 :=
  refute_split compatible supports domains172 targets172 0 [1] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected172_1, List.forall_mem_nil _⟩)
#print axioms rejected172
theorem rejected173 : ¬ Sat compatible supports domains173 targets173 :=
  refute_empty_domain compatible supports domains173 targets173 0 (by decide)
#print axioms rejected173
set_option maxRecDepth 8192 in
theorem child_rejected174_111 : ¬ Sat compatible supports (childDomains compatible supports domains174 targets174 8 111) (childTargets supports targets174 111) :=
  transport_child domains174 targets174 8 111 domains165 targets165 (by decide) (by decide) rejected165
set_option maxRecDepth 8192 in
theorem child_rejected174_115 : ¬ Sat compatible supports (childDomains compatible supports domains174 targets174 8 115) (childTargets supports targets174 115) :=
  transport_child domains174 targets174 8 115 domains170 targets170 (by decide) (by decide) rejected170
set_option maxRecDepth 8192 in
theorem child_rejected174_116 : ¬ Sat compatible supports (childDomains compatible supports domains174 targets174 8 116) (childTargets supports targets174 116) :=
  transport_child domains174 targets174 8 116 domains172 targets172 (by decide) (by decide) rejected172
set_option maxRecDepth 8192 in
theorem child_rejected174_118 : ¬ Sat compatible supports (childDomains compatible supports domains174 targets174 8 118) (childTargets supports targets174 118) :=
  transport_child domains174 targets174 8 118 domains173 targets173 (by decide) (by decide) rejected173
theorem rejected174 : ¬ Sat compatible supports domains174 targets174 :=
  refute_split compatible supports domains174 targets174 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected174_111, (List.forall_mem_cons.mpr ⟨child_rejected174_115, (List.forall_mem_cons.mpr ⟨child_rejected174_116, (List.forall_mem_cons.mpr ⟨child_rejected174_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected174
set_option maxRecDepth 8192 in
theorem child_rejected175_184 : ¬ Sat compatible supports (childDomains compatible supports domains175 targets175 12 184) (childTargets supports targets175 184) :=
  transport_child domains175 targets175 12 184 domains174 targets174 (by decide) (by decide) rejected174
theorem rejected175 : ¬ Sat compatible supports domains175 targets175 :=
  refute_split compatible supports domains175 targets175 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected175_184, List.forall_mem_nil _⟩)
#print axioms rejected175
end ElevenSquare.Pending.EncodedSearch
