import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes11
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected96_28 : ¬ Sat compatible supports (childDomains compatible supports domains96 targets96 2 28) (childTargets supports targets96 28) :=
  transport_child domains96 targets96 2 28 domains94 targets94 (by decide) (by decide) rejected94
set_option maxRecDepth 8192 in
theorem child_rejected96_29 : ¬ Sat compatible supports (childDomains compatible supports domains96 targets96 2 29) (childTargets supports targets96 29) :=
  transport_child domains96 targets96 2 29 domains95 targets95 (by decide) (by decide) rejected95
theorem rejected96 : ¬ Sat compatible supports domains96 targets96 :=
  refute_split compatible supports domains96 targets96 2 [28, 29] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected96_28, (List.forall_mem_cons.mpr ⟨child_rejected96_29, List.forall_mem_nil _⟩)⟩)
#print axioms rejected96
theorem rejected97 : ¬ Sat compatible supports domains97 targets97 :=
  refute_empty_domain compatible supports domains97 targets97 2 (by decide)
#print axioms rejected97
theorem rejected98 : ¬ Sat compatible supports domains98 targets98 :=
  refute_empty_domain compatible supports domains98 targets98 2 (by decide)
#print axioms rejected98
theorem rejected99 : ¬ Sat compatible supports domains99 targets99 :=
  refute_empty_domain compatible supports domains99 targets99 2 (by decide)
#print axioms rejected99
theorem rejected100 : ¬ Sat compatible supports domains100 targets100 :=
  refute_empty_domain compatible supports domains100 targets100 2 (by decide)
#print axioms rejected100
theorem rejected101 : ¬ Sat compatible supports domains101 targets101 :=
  refute_empty_domain compatible supports domains101 targets101 4 (by decide)
#print axioms rejected101
theorem rejected102 : ¬ Sat compatible supports domains102 targets102 :=
  refute_empty_domain compatible supports domains102 targets102 4 (by decide)
#print axioms rejected102
set_option maxRecDepth 8192 in
theorem child_rejected103_5 : ¬ Sat compatible supports (childDomains compatible supports domains103 targets103 0 5) (childTargets supports targets103 5) :=
  transport_child domains103 targets103 0 5 domains101 targets101 (by decide) (by decide) rejected101
set_option maxRecDepth 8192 in
theorem child_rejected103_8 : ¬ Sat compatible supports (childDomains compatible supports domains103 targets103 0 8) (childTargets supports targets103 8) :=
  transport_child domains103 targets103 0 8 domains102 targets102 (by decide) (by decide) rejected102
theorem rejected103 : ¬ Sat compatible supports domains103 targets103 :=
  refute_split compatible supports domains103 targets103 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected103_5, (List.forall_mem_cons.mpr ⟨child_rejected103_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected103
end ElevenSquare.Pending.EncodedSearch
