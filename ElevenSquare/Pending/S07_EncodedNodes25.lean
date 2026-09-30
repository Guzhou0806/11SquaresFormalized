import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes24
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected200 : ¬ Sat compatible supports domains200 targets200 :=
  refute_empty_domain compatible supports domains200 targets200 13 (by decide)
#print axioms rejected200
set_option maxRecDepth 8192 in
theorem child_rejected201_206 : ¬ Sat compatible supports (childDomains compatible supports domains201 targets201 14 206) (childTargets supports targets201 206) :=
  transport_child domains201 targets201 14 206 domains200 targets200 (by decide) (by decide) rejected200
theorem rejected201 : ¬ Sat compatible supports domains201 targets201 :=
  refute_split compatible supports domains201 targets201 14 [206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected201_206, List.forall_mem_nil _⟩)
#print axioms rejected201
set_option maxRecDepth 8192 in
theorem child_rejected202_117 : ¬ Sat compatible supports (childDomains compatible supports domains202 targets202 8 117) (childTargets supports targets202 117) :=
  transport_child domains202 targets202 8 117 domains199 targets199 (by decide) (by decide) rejected199
set_option maxRecDepth 8192 in
theorem child_rejected202_123 : ¬ Sat compatible supports (childDomains compatible supports domains202 targets202 8 123) (childTargets supports targets202 123) :=
  transport_child domains202 targets202 8 123 domains201 targets201 (by decide) (by decide) rejected201
theorem rejected202 : ¬ Sat compatible supports domains202 targets202 :=
  refute_split compatible supports domains202 targets202 8 [117, 123] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected202_117, (List.forall_mem_cons.mpr ⟨child_rejected202_123, List.forall_mem_nil _⟩)⟩)
#print axioms rejected202
set_option maxRecDepth 8192 in
theorem child_rejected203_5 : ¬ Sat compatible supports (childDomains compatible supports domains203 targets203 0 5) (childTargets supports targets203 5) :=
  transport_child domains203 targets203 0 5 domains196 targets196 (by decide) (by decide) rejected196
set_option maxRecDepth 8192 in
theorem child_rejected203_8 : ¬ Sat compatible supports (childDomains compatible supports domains203 targets203 0 8) (childTargets supports targets203 8) :=
  transport_child domains203 targets203 0 8 domains202 targets202 (by decide) (by decide) rejected202
theorem rejected203 : ¬ Sat compatible supports domains203 targets203 :=
  refute_split compatible supports domains203 targets203 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected203_5, (List.forall_mem_cons.mpr ⟨child_rejected203_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected203
set_option maxRecDepth 8192 in
theorem child_rejected204_217 : ¬ Sat compatible supports (childDomains compatible supports domains204 targets204 15 217) (childTargets supports targets204 217) :=
  transport_child domains204 targets204 15 217 domains203 targets203 (by decide) (by decide) rejected203
theorem rejected204 : ¬ Sat compatible supports domains204 targets204 :=
  refute_split compatible supports domains204 targets204 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected204_217, List.forall_mem_nil _⟩)
#print axioms rejected204
theorem rejected205 : ¬ Sat compatible supports domains205 targets205 :=
  refute_empty_domain compatible supports domains205 targets205 9 (by decide)
#print axioms rejected205
theorem rejected206 : ¬ Sat compatible supports domains206 targets206 :=
  refute_empty_domain compatible supports domains206 targets206 9 (by decide)
#print axioms rejected206
set_option maxRecDepth 8192 in
theorem child_rejected207_65 : ¬ Sat compatible supports (childDomains compatible supports domains207 targets207 5 65) (childTargets supports targets207 65) :=
  transport_child domains207 targets207 5 65 domains205 targets205 (by decide) (by decide) rejected205
set_option maxRecDepth 8192 in
theorem child_rejected207_70 : ¬ Sat compatible supports (childDomains compatible supports domains207 targets207 5 70) (childTargets supports targets207 70) :=
  transport_child domains207 targets207 5 70 domains206 targets206 (by decide) (by decide) rejected206
theorem rejected207 : ¬ Sat compatible supports domains207 targets207 :=
  refute_split compatible supports domains207 targets207 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected207_65, (List.forall_mem_cons.mpr ⟨child_rejected207_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected207
end ElevenSquare.Pending.EncodedSearch
