import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes1
import ElevenSquare.Pending.S07_EncodedNodes2
import ElevenSquare.Pending.S07_EncodedNodes4
import ElevenSquare.Pending.S07_EncodedNodes6
import ElevenSquare.Pending.S07_EncodedNodes11
import ElevenSquare.Pending.S07_EncodedNodes12
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected104 : ¬ Sat compatible supports domains104 targets104 :=
  refute_empty_domain compatible supports domains104 targets104 2 (by decide)
#print axioms rejected104
theorem rejected105 : ¬ Sat compatible supports domains105 targets105 :=
  refute_empty_domain compatible supports domains105 targets105 2 (by decide)
#print axioms rejected105
set_option maxRecDepth 8192 in
theorem child_rejected106_5 : ¬ Sat compatible supports (childDomains compatible supports domains106 targets106 0 5) (childTargets supports targets106 5) :=
  transport_child domains106 targets106 0 5 domains104 targets104 (by decide) (by decide) rejected104
set_option maxRecDepth 8192 in
theorem child_rejected106_8 : ¬ Sat compatible supports (childDomains compatible supports domains106 targets106 0 8) (childTargets supports targets106 8) :=
  transport_child domains106 targets106 0 8 domains105 targets105 (by decide) (by decide) rejected105
theorem rejected106 : ¬ Sat compatible supports domains106 targets106 :=
  refute_split compatible supports domains106 targets106 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected106_5, (List.forall_mem_cons.mpr ⟨child_rejected106_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected106
set_option maxRecDepth 8192 in
theorem child_rejected107_12 : ¬ Sat compatible supports (childDomains compatible supports domains107 targets107 1 12) (childTargets supports targets107 12) :=
  transport_child domains107 targets107 1 12 domains96 targets96 (by decide) (by decide) rejected96
set_option maxRecDepth 8192 in
theorem child_rejected107_13 : ¬ Sat compatible supports (childDomains compatible supports domains107 targets107 1 13) (childTargets supports targets107 13) :=
  transport_child domains107 targets107 1 13 domains97 targets97 (by decide) (by decide) rejected97
set_option maxRecDepth 8192 in
theorem child_rejected107_15 : ¬ Sat compatible supports (childDomains compatible supports domains107 targets107 1 15) (childTargets supports targets107 15) :=
  transport_child domains107 targets107 1 15 domains98 targets98 (by decide) (by decide) rejected98
set_option maxRecDepth 8192 in
theorem child_rejected107_16 : ¬ Sat compatible supports (childDomains compatible supports domains107 targets107 1 16) (childTargets supports targets107 16) :=
  transport_child domains107 targets107 1 16 domains99 targets99 (by decide) (by decide) rejected99
set_option maxRecDepth 8192 in
theorem child_rejected107_17 : ¬ Sat compatible supports (childDomains compatible supports domains107 targets107 1 17) (childTargets supports targets107 17) :=
  transport_child domains107 targets107 1 17 domains100 targets100 (by decide) (by decide) rejected100
set_option maxRecDepth 8192 in
theorem child_rejected107_18 : ¬ Sat compatible supports (childDomains compatible supports domains107 targets107 1 18) (childTargets supports targets107 18) :=
  transport_child domains107 targets107 1 18 domains103 targets103 (by decide) (by decide) rejected103
set_option maxRecDepth 8192 in
theorem child_rejected107_19 : ¬ Sat compatible supports (childDomains compatible supports domains107 targets107 1 19) (childTargets supports targets107 19) :=
  transport_child domains107 targets107 1 19 domains106 targets106 (by decide) (by decide) rejected106
theorem rejected107 : ¬ Sat compatible supports domains107 targets107 :=
  refute_split compatible supports domains107 targets107 1 [12, 13, 15, 16, 17, 18, 19] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected107_12, (List.forall_mem_cons.mpr ⟨child_rejected107_13, (List.forall_mem_cons.mpr ⟨child_rejected107_15, (List.forall_mem_cons.mpr ⟨child_rejected107_16, (List.forall_mem_cons.mpr ⟨child_rejected107_17, (List.forall_mem_cons.mpr ⟨child_rejected107_18, (List.forall_mem_cons.mpr ⟨child_rejected107_19, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected107
set_option maxRecDepth 8192 in
theorem child_rejected108_180 : ¬ Sat compatible supports (childDomains compatible supports domains108 targets108 12 180) (childTargets supports targets108 180) :=
  transport_child domains108 targets108 12 180 domains8 targets8 (by decide) (by decide) rejected8
set_option maxRecDepth 8192 in
theorem child_rejected108_181 : ¬ Sat compatible supports (childDomains compatible supports domains108 targets108 12 181) (childTargets supports targets108 181) :=
  transport_child domains108 targets108 12 181 domains17 targets17 (by decide) (by decide) rejected17
set_option maxRecDepth 8192 in
theorem child_rejected108_182 : ¬ Sat compatible supports (childDomains compatible supports domains108 targets108 12 182) (childTargets supports targets108 182) :=
  transport_child domains108 targets108 12 182 domains32 targets32 (by decide) (by decide) rejected32
set_option maxRecDepth 8192 in
theorem child_rejected108_183 : ¬ Sat compatible supports (childDomains compatible supports domains108 targets108 12 183) (childTargets supports targets108 183) :=
  transport_child domains108 targets108 12 183 domains51 targets51 (by decide) (by decide) rejected51
set_option maxRecDepth 8192 in
theorem child_rejected108_184 : ¬ Sat compatible supports (childDomains compatible supports domains108 targets108 12 184) (childTargets supports targets108 184) :=
  transport_child domains108 targets108 12 184 domains93 targets93 (by decide) (by decide) rejected93
set_option maxRecDepth 8192 in
theorem child_rejected108_185 : ¬ Sat compatible supports (childDomains compatible supports domains108 targets108 12 185) (childTargets supports targets108 185) :=
  transport_child domains108 targets108 12 185 domains107 targets107 (by decide) (by decide) rejected107
theorem rejected108 : ¬ Sat compatible supports domains108 targets108 :=
  refute_split compatible supports domains108 targets108 12 [180, 181, 182, 183, 184, 185] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected108_180, (List.forall_mem_cons.mpr ⟨child_rejected108_181, (List.forall_mem_cons.mpr ⟨child_rejected108_182, (List.forall_mem_cons.mpr ⟨child_rejected108_183, (List.forall_mem_cons.mpr ⟨child_rejected108_184, (List.forall_mem_cons.mpr ⟨child_rejected108_185, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected108
theorem rejected109 : ¬ Sat compatible supports domains109 targets109 :=
  refute_empty_domain compatible supports domains109 targets109 13 (by decide)
#print axioms rejected109
theorem rejected110 : ¬ Sat compatible supports domains110 targets110 :=
  refute_empty_domain compatible supports domains110 targets110 1 (by decide)
#print axioms rejected110
theorem rejected111 : ¬ Sat compatible supports domains111 targets111 :=
  refute_empty_domain compatible supports domains111 targets111 1 (by decide)
#print axioms rejected111
end ElevenSquare.Pending.EncodedSearch
