import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected184 : ¬ Sat compatible supports domains184 targets184 :=
  refute_empty_domain compatible supports domains184 targets184 9 (by decide)
#print axioms rejected184
set_option maxRecDepth 8192 in
theorem child_rejected185_70 : ¬ Sat compatible supports (childDomains compatible supports domains185 targets185 5 70) (childTargets supports targets185 70) :=
  transport_child domains185 targets185 5 70 domains184 targets184 (by decide) (by decide) rejected184
theorem rejected185 : ¬ Sat compatible supports domains185 targets185 :=
  refute_split compatible supports domains185 targets185 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected185_70, List.forall_mem_nil _⟩)
#print axioms rejected185
theorem rejected186 : ¬ Sat compatible supports domains186 targets186 :=
  refute_empty_domain compatible supports domains186 targets186 9 (by decide)
#print axioms rejected186
set_option maxRecDepth 8192 in
theorem child_rejected187_70 : ¬ Sat compatible supports (childDomains compatible supports domains187 targets187 5 70) (childTargets supports targets187 70) :=
  transport_child domains187 targets187 5 70 domains186 targets186 (by decide) (by decide) rejected186
theorem rejected187 : ¬ Sat compatible supports domains187 targets187 :=
  refute_split compatible supports domains187 targets187 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected187_70, List.forall_mem_nil _⟩)
#print axioms rejected187
set_option maxRecDepth 8192 in
theorem child_rejected188_5 : ¬ Sat compatible supports (childDomains compatible supports domains188 targets188 0 5) (childTargets supports targets188 5) :=
  transport_child domains188 targets188 0 5 domains185 targets185 (by decide) (by decide) rejected185
set_option maxRecDepth 8192 in
theorem child_rejected188_8 : ¬ Sat compatible supports (childDomains compatible supports domains188 targets188 0 8) (childTargets supports targets188 8) :=
  transport_child domains188 targets188 0 8 domains187 targets187 (by decide) (by decide) rejected187
theorem rejected188 : ¬ Sat compatible supports domains188 targets188 :=
  refute_split compatible supports domains188 targets188 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected188_5, (List.forall_mem_cons.mpr ⟨child_rejected188_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected188
theorem rejected189 : ¬ Sat compatible supports domains189 targets189 :=
  refute_empty_domain compatible supports domains189 targets189 5 (by decide)
#print axioms rejected189
theorem rejected190 : ¬ Sat compatible supports domains190 targets190 :=
  refute_empty_domain compatible supports domains190 targets190 13 (by decide)
#print axioms rejected190
set_option maxRecDepth 8192 in
theorem child_rejected191_140 : ¬ Sat compatible supports (childDomains compatible supports domains191 targets191 9 140) (childTargets supports targets191 140) :=
  transport_child domains191 targets191 9 140 domains190 targets190 (by decide) (by decide) rejected190
theorem rejected191 : ¬ Sat compatible supports domains191 targets191 :=
  refute_split compatible supports domains191 targets191 9 [140] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected191_140, List.forall_mem_nil _⟩)
#print axioms rejected191
end ElevenSquare.Pending.EncodedSearch
