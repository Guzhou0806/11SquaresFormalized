import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected120 : ¬ Sat compatible supports domains120 targets120 :=
  refute_empty_domain compatible supports domains120 targets120 14 (by decide)
#print axioms rejected120
theorem rejected121 : ¬ Sat compatible supports domains121 targets121 :=
  refute_empty_domain compatible supports domains121 targets121 9 (by decide)
#print axioms rejected121
theorem rejected122 : ¬ Sat compatible supports domains122 targets122 :=
  refute_empty_domain compatible supports domains122 targets122 6 (by decide)
#print axioms rejected122
theorem rejected123 : ¬ Sat compatible supports domains123 targets123 :=
  refute_empty_domain compatible supports domains123 targets123 9 (by decide)
#print axioms rejected123
set_option maxRecDepth 8192 in
theorem child_rejected124_200 : ¬ Sat compatible supports (childDomains compatible supports domains124 targets124 14 200) (childTargets supports targets124 200) :=
  transport_child domains124 targets124 14 200 domains122 targets122 (by decide) (by decide) rejected122
set_option maxRecDepth 8192 in
theorem child_rejected124_201 : ¬ Sat compatible supports (childDomains compatible supports domains124 targets124 14 201) (childTargets supports targets124 201) :=
  transport_child domains124 targets124 14 201 domains123 targets123 (by decide) (by decide) rejected123
theorem rejected124 : ¬ Sat compatible supports domains124 targets124 :=
  refute_split compatible supports domains124 targets124 14 [200, 201] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected124_200, (List.forall_mem_cons.mpr ⟨child_rejected124_201, List.forall_mem_nil _⟩)⟩)
#print axioms rejected124
theorem rejected125 : ¬ Sat compatible supports domains125 targets125 :=
  refute_empty_domain compatible supports domains125 targets125 6 (by decide)
#print axioms rejected125
theorem rejected126 : ¬ Sat compatible supports domains126 targets126 :=
  refute_empty_domain compatible supports domains126 targets126 11 (by decide)
#print axioms rejected126
set_option maxRecDepth 8192 in
theorem child_rejected127_92 : ¬ Sat compatible supports (childDomains compatible supports domains127 targets127 6 92) (childTargets supports targets127 92) :=
  transport_child domains127 targets127 6 92 domains126 targets126 (by decide) (by decide) rejected126
theorem rejected127 : ¬ Sat compatible supports domains127 targets127 :=
  refute_split compatible supports domains127 targets127 6 [92] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected127_92, List.forall_mem_nil _⟩)
#print axioms rejected127
end ElevenSquare.Pending.EncodedSearch
