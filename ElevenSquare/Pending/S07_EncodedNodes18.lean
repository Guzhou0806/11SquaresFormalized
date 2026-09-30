import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes14
import ElevenSquare.Pending.S07_EncodedNodes16
import ElevenSquare.Pending.S07_EncodedNodes17
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected144 : ¬ Sat compatible supports domains144 targets144 :=
  refute_empty_domain compatible supports domains144 targets144 13 (by decide)
#print axioms rejected144
theorem rejected145 : ¬ Sat compatible supports domains145 targets145 :=
  refute_empty_domain compatible supports domains145 targets145 13 (by decide)
#print axioms rejected145
theorem rejected146 : ¬ Sat compatible supports domains146 targets146 :=
  refute_empty_domain compatible supports domains146 targets146 14 (by decide)
#print axioms rejected146
set_option maxRecDepth 8192 in
theorem child_rejected147_194 : ¬ Sat compatible supports (childDomains compatible supports domains147 targets147 13 194) (childTargets supports targets147 194) :=
  transport_child domains147 targets147 13 194 domains146 targets146 (by decide) (by decide) rejected146
theorem rejected147 : ¬ Sat compatible supports domains147 targets147 :=
  refute_split compatible supports domains147 targets147 13 [194] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected147_194, List.forall_mem_nil _⟩)
#print axioms rejected147
theorem rejected148 : ¬ Sat compatible supports domains148 targets148 :=
  refute_empty_domain compatible supports domains148 targets148 13 (by decide)
#print axioms rejected148
set_option maxRecDepth 8192 in
theorem child_rejected149_111 : ¬ Sat compatible supports (childDomains compatible supports domains149 targets149 8 111) (childTargets supports targets149 111) :=
  transport_child domains149 targets149 8 111 domains144 targets144 (by decide) (by decide) rejected144
set_option maxRecDepth 8192 in
theorem child_rejected149_115 : ¬ Sat compatible supports (childDomains compatible supports domains149 targets149 8 115) (childTargets supports targets149 115) :=
  transport_child domains149 targets149 8 115 domains145 targets145 (by decide) (by decide) rejected145
set_option maxRecDepth 8192 in
theorem child_rejected149_116 : ¬ Sat compatible supports (childDomains compatible supports domains149 targets149 8 116) (childTargets supports targets149 116) :=
  transport_child domains149 targets149 8 116 domains147 targets147 (by decide) (by decide) rejected147
set_option maxRecDepth 8192 in
theorem child_rejected149_118 : ¬ Sat compatible supports (childDomains compatible supports domains149 targets149 8 118) (childTargets supports targets149 118) :=
  transport_child domains149 targets149 8 118 domains148 targets148 (by decide) (by decide) rejected148
theorem rejected149 : ¬ Sat compatible supports domains149 targets149 :=
  refute_split compatible supports domains149 targets149 8 [111, 115, 116, 118] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected149_111, (List.forall_mem_cons.mpr ⟨child_rejected149_115, (List.forall_mem_cons.mpr ⟨child_rejected149_116, (List.forall_mem_cons.mpr ⟨child_rejected149_118, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected149
set_option maxRecDepth 8192 in
theorem child_rejected150_180 : ¬ Sat compatible supports (childDomains compatible supports domains150 targets150 12 180) (childTargets supports targets150 180) :=
  transport_child domains150 targets150 12 180 domains117 targets117 (by decide) (by decide) rejected117
set_option maxRecDepth 8192 in
theorem child_rejected150_181 : ¬ Sat compatible supports (childDomains compatible supports domains150 targets150 12 181) (childTargets supports targets150 181) :=
  transport_child domains150 targets150 12 181 domains118 targets118 (by decide) (by decide) rejected118
set_option maxRecDepth 8192 in
theorem child_rejected150_182 : ¬ Sat compatible supports (childDomains compatible supports domains150 targets150 12 182) (childTargets supports targets150 182) :=
  transport_child domains150 targets150 12 182 domains133 targets133 (by decide) (by decide) rejected133
set_option maxRecDepth 8192 in
theorem child_rejected150_183 : ¬ Sat compatible supports (childDomains compatible supports domains150 targets150 12 183) (childTargets supports targets150 183) :=
  transport_child domains150 targets150 12 183 domains134 targets134 (by decide) (by decide) rejected134
set_option maxRecDepth 8192 in
theorem child_rejected150_184 : ¬ Sat compatible supports (childDomains compatible supports domains150 targets150 12 184) (childTargets supports targets150 184) :=
  transport_child domains150 targets150 12 184 domains143 targets143 (by decide) (by decide) rejected143
set_option maxRecDepth 8192 in
theorem child_rejected150_185 : ¬ Sat compatible supports (childDomains compatible supports domains150 targets150 12 185) (childTargets supports targets150 185) :=
  transport_child domains150 targets150 12 185 domains149 targets149 (by decide) (by decide) rejected149
theorem rejected150 : ¬ Sat compatible supports domains150 targets150 :=
  refute_split compatible supports domains150 targets150 12 [180, 181, 182, 183, 184, 185] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected150_180, (List.forall_mem_cons.mpr ⟨child_rejected150_181, (List.forall_mem_cons.mpr ⟨child_rejected150_182, (List.forall_mem_cons.mpr ⟨child_rejected150_183, (List.forall_mem_cons.mpr ⟨child_rejected150_184, (List.forall_mem_cons.mpr ⟨child_rejected150_185, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected150
theorem rejected151 : ¬ Sat compatible supports domains151 targets151 :=
  refute_empty_domain compatible supports domains151 targets151 8 (by decide)
#print axioms rejected151
end ElevenSquare.Pending.EncodedSearch
