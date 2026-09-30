import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes14
import ElevenSquare.Pending.S07_EncodedNodes15
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected128_128 : ¬ Sat compatible supports (childDomains compatible supports domains128 targets128 9 128) (childTargets supports targets128 128) :=
  transport_child domains128 targets128 9 128 domains127 targets127 (by decide) (by decide) rejected127
theorem rejected128 : ¬ Sat compatible supports domains128 targets128 :=
  refute_split compatible supports domains128 targets128 9 [128] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected128_128, List.forall_mem_nil _⟩)
#print axioms rejected128
set_option maxRecDepth 8192 in
theorem child_rejected129_8 : ¬ Sat compatible supports (childDomains compatible supports domains129 targets129 0 8) (childTargets supports targets129 8) :=
  transport_child domains129 targets129 0 8 domains128 targets128 (by decide) (by decide) rejected128
theorem rejected129 : ¬ Sat compatible supports domains129 targets129 :=
  refute_split compatible supports domains129 targets129 0 [8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected129_8, List.forall_mem_nil _⟩)
#print axioms rejected129
set_option maxRecDepth 8192 in
theorem child_rejected130_200 : ¬ Sat compatible supports (childDomains compatible supports domains130 targets130 14 200) (childTargets supports targets130 200) :=
  transport_child domains130 targets130 14 200 domains125 targets125 (by decide) (by decide) rejected125
set_option maxRecDepth 8192 in
theorem child_rejected130_201 : ¬ Sat compatible supports (childDomains compatible supports domains130 targets130 14 201) (childTargets supports targets130 201) :=
  transport_child domains130 targets130 14 201 domains129 targets129 (by decide) (by decide) rejected129
theorem rejected130 : ¬ Sat compatible supports domains130 targets130 :=
  refute_split compatible supports domains130 targets130 14 [200, 201] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected130_200, (List.forall_mem_cons.mpr ⟨child_rejected130_201, List.forall_mem_nil _⟩)⟩)
#print axioms rejected130
set_option maxRecDepth 8192 in
theorem child_rejected131_122 : ¬ Sat compatible supports (childDomains compatible supports domains131 targets131 8 122) (childTargets supports targets131 122) :=
  transport_child domains131 targets131 8 122 domains124 targets124 (by decide) (by decide) rejected124
set_option maxRecDepth 8192 in
theorem child_rejected131_123 : ¬ Sat compatible supports (childDomains compatible supports domains131 targets131 8 123) (childTargets supports targets131 123) :=
  transport_child domains131 targets131 8 123 domains130 targets130 (by decide) (by decide) rejected130
theorem rejected131 : ¬ Sat compatible supports domains131 targets131 :=
  refute_split compatible supports domains131 targets131 8 [122, 123] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected131_122, (List.forall_mem_cons.mpr ⟨child_rejected131_123, List.forall_mem_nil _⟩)⟩)
#print axioms rejected131
theorem rejected132 : ¬ Sat compatible supports domains132 targets132 :=
  refute_empty_domain compatible supports domains132 targets132 14 (by decide)
#print axioms rejected132
set_option maxRecDepth 8192 in
theorem child_rejected133_187 : ¬ Sat compatible supports (childDomains compatible supports domains133 targets133 13 187) (childTargets supports targets133 187) :=
  transport_child domains133 targets133 13 187 domains119 targets119 (by decide) (by decide) rejected119
set_option maxRecDepth 8192 in
theorem child_rejected133_189 : ¬ Sat compatible supports (childDomains compatible supports domains133 targets133 13 189) (childTargets supports targets133 189) :=
  transport_child domains133 targets133 13 189 domains120 targets120 (by decide) (by decide) rejected120
set_option maxRecDepth 8192 in
theorem child_rejected133_191 : ¬ Sat compatible supports (childDomains compatible supports domains133 targets133 13 191) (childTargets supports targets133 191) :=
  transport_child domains133 targets133 13 191 domains121 targets121 (by decide) (by decide) rejected121
set_option maxRecDepth 8192 in
theorem child_rejected133_193 : ¬ Sat compatible supports (childDomains compatible supports domains133 targets133 13 193) (childTargets supports targets133 193) :=
  transport_child domains133 targets133 13 193 domains131 targets131 (by decide) (by decide) rejected131
set_option maxRecDepth 8192 in
theorem child_rejected133_194 : ¬ Sat compatible supports (childDomains compatible supports domains133 targets133 13 194) (childTargets supports targets133 194) :=
  transport_child domains133 targets133 13 194 domains132 targets132 (by decide) (by decide) rejected132
theorem rejected133 : ¬ Sat compatible supports domains133 targets133 :=
  refute_split compatible supports domains133 targets133 13 [187, 189, 191, 193, 194] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected133_187, (List.forall_mem_cons.mpr ⟨child_rejected133_189, (List.forall_mem_cons.mpr ⟨child_rejected133_191, (List.forall_mem_cons.mpr ⟨child_rejected133_193, (List.forall_mem_cons.mpr ⟨child_rejected133_194, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
#print axioms rejected133
theorem rejected134 : ¬ Sat compatible supports domains134 targets134 :=
  refute_empty_domain compatible supports domains134 targets134 13 (by decide)
#print axioms rejected134
theorem rejected135 : ¬ Sat compatible supports domains135 targets135 :=
  refute_empty_domain compatible supports domains135 targets135 13 (by decide)
#print axioms rejected135
end ElevenSquare.Pending.EncodedSearch
