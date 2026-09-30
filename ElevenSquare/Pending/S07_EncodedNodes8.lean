import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes6
import ElevenSquare.Pending.S07_EncodedNodes7
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected64_202 : ¬ Sat compatible supports (childDomains compatible supports domains64 targets64 14 202) (childTargets supports targets64 202) :=
  transport_child domains64 targets64 14 202 domains53 targets53 (by decide) (by decide) rejected53
set_option maxRecDepth 8192 in
theorem child_rejected64_205 : ¬ Sat compatible supports (childDomains compatible supports domains64 targets64 14 205) (childTargets supports targets64 205) :=
  transport_child domains64 targets64 14 205 domains56 targets56 (by decide) (by decide) rejected56
set_option maxRecDepth 8192 in
theorem child_rejected64_206 : ¬ Sat compatible supports (childDomains compatible supports domains64 targets64 14 206) (childTargets supports targets64 206) :=
  transport_child domains64 targets64 14 206 domains63 targets63 (by decide) (by decide) rejected63
theorem rejected64 : ¬ Sat compatible supports domains64 targets64 :=
  refute_split compatible supports domains64 targets64 14 [202, 205, 206] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected64_202, (List.forall_mem_cons.mpr ⟨child_rejected64_205, (List.forall_mem_cons.mpr ⟨child_rejected64_206, List.forall_mem_nil _⟩)⟩)⟩)
#print axioms rejected64
theorem rejected65 : ¬ Sat compatible supports domains65 targets65 :=
  refute_empty_domain compatible supports domains65 targets65 4 (by decide)
#print axioms rejected65
set_option maxRecDepth 8192 in
theorem child_rejected66_8 : ¬ Sat compatible supports (childDomains compatible supports domains66 targets66 0 8) (childTargets supports targets66 8) :=
  transport_child domains66 targets66 0 8 domains65 targets65 (by decide) (by decide) rejected65
theorem rejected66 : ¬ Sat compatible supports domains66 targets66 :=
  refute_split compatible supports domains66 targets66 0 [8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected66_8, List.forall_mem_nil _⟩)
#print axioms rejected66
theorem rejected67 : ¬ Sat compatible supports domains67 targets67 :=
  refute_empty_domain compatible supports domains67 targets67 0 (by decide)
#print axioms rejected67
set_option maxRecDepth 8192 in
theorem child_rejected68_21 : ¬ Sat compatible supports (childDomains compatible supports domains68 targets68 2 21) (childTargets supports targets68 21) :=
  transport_child domains68 targets68 2 21 domains66 targets66 (by decide) (by decide) rejected66
set_option maxRecDepth 8192 in
theorem child_rejected68_33 : ¬ Sat compatible supports (childDomains compatible supports domains68 targets68 2 33) (childTargets supports targets68 33) :=
  transport_child domains68 targets68 2 33 domains67 targets67 (by decide) (by decide) rejected67
theorem rejected68 : ¬ Sat compatible supports domains68 targets68 :=
  refute_split compatible supports domains68 targets68 2 [21, 33] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected68_21, (List.forall_mem_cons.mpr ⟨child_rejected68_33, List.forall_mem_nil _⟩)⟩)
#print axioms rejected68
theorem rejected69 : ¬ Sat compatible supports domains69 targets69 :=
  refute_empty_domain compatible supports domains69 targets69 2 (by decide)
#print axioms rejected69
theorem rejected70 : ¬ Sat compatible supports domains70 targets70 :=
  refute_empty_domain compatible supports domains70 targets70 4 (by decide)
#print axioms rejected70
theorem rejected71 : ¬ Sat compatible supports domains71 targets71 :=
  refute_empty_domain compatible supports domains71 targets71 10 (by decide)
#print axioms rejected71
end ElevenSquare.Pending.EncodedSearch
