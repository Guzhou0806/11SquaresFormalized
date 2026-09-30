import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes25
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected208 : ¬ Sat compatible supports domains208 targets208 :=
  refute_empty_domain compatible supports domains208 targets208 9 (by decide)
#print axioms rejected208
theorem rejected209 : ¬ Sat compatible supports domains209 targets209 :=
  refute_empty_domain compatible supports domains209 targets209 9 (by decide)
#print axioms rejected209
set_option maxRecDepth 8192 in
theorem child_rejected210_65 : ¬ Sat compatible supports (childDomains compatible supports domains210 targets210 5 65) (childTargets supports targets210 65) :=
  transport_child domains210 targets210 5 65 domains208 targets208 (by decide) (by decide) rejected208
set_option maxRecDepth 8192 in
theorem child_rejected210_70 : ¬ Sat compatible supports (childDomains compatible supports domains210 targets210 5 70) (childTargets supports targets210 70) :=
  transport_child domains210 targets210 5 70 domains209 targets209 (by decide) (by decide) rejected209
theorem rejected210 : ¬ Sat compatible supports domains210 targets210 :=
  refute_split compatible supports domains210 targets210 5 [65, 70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected210_65, (List.forall_mem_cons.mpr ⟨child_rejected210_70, List.forall_mem_nil _⟩)⟩)
#print axioms rejected210
set_option maxRecDepth 8192 in
theorem child_rejected211_5 : ¬ Sat compatible supports (childDomains compatible supports domains211 targets211 0 5) (childTargets supports targets211 5) :=
  transport_child domains211 targets211 0 5 domains207 targets207 (by decide) (by decide) rejected207
set_option maxRecDepth 8192 in
theorem child_rejected211_8 : ¬ Sat compatible supports (childDomains compatible supports domains211 targets211 0 8) (childTargets supports targets211 8) :=
  transport_child domains211 targets211 0 8 domains210 targets210 (by decide) (by decide) rejected210
theorem rejected211 : ¬ Sat compatible supports domains211 targets211 :=
  refute_split compatible supports domains211 targets211 0 [5, 8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected211_5, (List.forall_mem_cons.mpr ⟨child_rejected211_8, List.forall_mem_nil _⟩)⟩)
#print axioms rejected211
set_option maxRecDepth 8192 in
theorem child_rejected212_217 : ¬ Sat compatible supports (childDomains compatible supports domains212 targets212 15 217) (childTargets supports targets212 217) :=
  transport_child domains212 targets212 15 217 domains211 targets211 (by decide) (by decide) rejected211
theorem rejected212 : ¬ Sat compatible supports domains212 targets212 :=
  refute_split compatible supports domains212 targets212 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected212_217, List.forall_mem_nil _⟩)
#print axioms rejected212
theorem rejected213 : ¬ Sat compatible supports domains213 targets213 :=
  refute_empty_domain compatible supports domains213 targets213 5 (by decide)
#print axioms rejected213
theorem rejected214 : ¬ Sat compatible supports domains214 targets214 :=
  refute_empty_domain compatible supports domains214 targets214 6 (by decide)
#print axioms rejected214
theorem rejected215 : ¬ Sat compatible supports domains215 targets215 :=
  refute_empty_domain compatible supports domains215 targets215 8 (by decide)
#print axioms rejected215
end ElevenSquare.Pending.EncodedSearch
