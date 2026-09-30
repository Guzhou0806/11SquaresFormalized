import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected152 : ¬ Sat compatible supports domains152 targets152 :=
  refute_empty_domain compatible supports domains152 targets152 11 (by decide)
#print axioms rejected152
set_option maxRecDepth 8192 in
theorem child_rejected153_92 : ¬ Sat compatible supports (childDomains compatible supports domains153 targets153 6 92) (childTargets supports targets153 92) :=
  transport_child domains153 targets153 6 92 domains152 targets152 (by decide) (by decide) rejected152
theorem rejected153 : ¬ Sat compatible supports domains153 targets153 :=
  refute_split compatible supports domains153 targets153 6 [92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected153_92, List.forall_mem_nil _⟩)
#print axioms rejected153
set_option maxRecDepth 8192 in
theorem child_rejected154_70 : ¬ Sat compatible supports (childDomains compatible supports domains154 targets154 5 70) (childTargets supports targets154 70) :=
  transport_child domains154 targets154 5 70 domains153 targets153 (by decide) (by decide) rejected153
theorem rejected154 : ¬ Sat compatible supports domains154 targets154 :=
  refute_split compatible supports domains154 targets154 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected154_70, List.forall_mem_nil _⟩)
#print axioms rejected154
theorem rejected155 : ¬ Sat compatible supports domains155 targets155 :=
  refute_empty_domain compatible supports domains155 targets155 8 (by decide)
#print axioms rejected155
theorem rejected156 : ¬ Sat compatible supports domains156 targets156 :=
  refute_empty_domain compatible supports domains156 targets156 11 (by decide)
#print axioms rejected156
set_option maxRecDepth 8192 in
theorem child_rejected157_92 : ¬ Sat compatible supports (childDomains compatible supports domains157 targets157 6 92) (childTargets supports targets157 92) :=
  transport_child domains157 targets157 6 92 domains156 targets156 (by decide) (by decide) rejected156
theorem rejected157 : ¬ Sat compatible supports domains157 targets157 :=
  refute_split compatible supports domains157 targets157 6 [92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected157_92, List.forall_mem_nil _⟩)
#print axioms rejected157
set_option maxRecDepth 8192 in
theorem child_rejected158_70 : ¬ Sat compatible supports (childDomains compatible supports domains158 targets158 5 70) (childTargets supports targets158 70) :=
  transport_child domains158 targets158 5 70 domains157 targets157 (by decide) (by decide) rejected157
theorem rejected158 : ¬ Sat compatible supports domains158 targets158 :=
  refute_split compatible supports domains158 targets158 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected158_70, List.forall_mem_nil _⟩)
#print axioms rejected158
theorem rejected159 : ¬ Sat compatible supports domains159 targets159 :=
  refute_empty_domain compatible supports domains159 targets159 11 (by decide)
#print axioms rejected159
end ElevenSquare.Pending.EncodedSearch
