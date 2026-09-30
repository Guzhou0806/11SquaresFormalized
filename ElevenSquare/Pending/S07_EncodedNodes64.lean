import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes63
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected512_29 : ¬ Sat compatible supports (childDomains compatible supports domains512 targets512 2 29) (childTargets supports targets512 29) :=
  transport_child domains512 targets512 2 29 domains511 targets511 (by decide) (by decide) rejected511
theorem rejected512 : ¬ Sat compatible supports domains512 targets512 :=
  refute_split compatible supports domains512 targets512 2 [29] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected512_29, List.forall_mem_nil _⟩)
#print axioms rejected512
set_option maxRecDepth 8192 in
theorem child_rejected513_187 : ¬ Sat compatible supports (childDomains compatible supports domains513 targets513 13 187) (childTargets supports targets513 187) :=
  transport_child domains513 targets513 13 187 domains505 targets505 (by decide) (by decide) rejected505
set_option maxRecDepth 8192 in
theorem child_rejected513_189 : ¬ Sat compatible supports (childDomains compatible supports domains513 targets513 13 189) (childTargets supports targets513 189) :=
  transport_child domains513 targets513 13 189 domains506 targets506 (by decide) (by decide) rejected506
set_option maxRecDepth 8192 in
theorem child_rejected513_191 : ¬ Sat compatible supports (childDomains compatible supports domains513 targets513 13 191) (childTargets supports targets513 191) :=
  transport_child domains513 targets513 13 191 domains507 targets507 (by decide) (by decide) rejected507
set_option maxRecDepth 8192 in
theorem child_rejected513_193 : ¬ Sat compatible supports (childDomains compatible supports domains513 targets513 13 193) (childTargets supports targets513 193) :=
  transport_child domains513 targets513 13 193 domains508 targets508 (by decide) (by decide) rejected508
set_option maxRecDepth 8192 in
theorem child_rejected513_194 : ¬ Sat compatible supports (childDomains compatible supports domains513 targets513 13 194) (childTargets supports targets513 194) :=
  transport_child domains513 targets513 13 194 domains512 targets512 (by decide) (by decide) rejected512
theorem rejected513 : ¬ Sat compatible supports domains513 targets513 :=
  refute_split compatible supports domains513 targets513 13 [187, 189, 191, 193, 194] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected513_187, (List.forall_mem_cons.mpr ⟨child_rejected513_189, (List.forall_mem_cons.mpr ⟨child_rejected513_191, (List.forall_mem_cons.mpr ⟨child_rejected513_193, (List.forall_mem_cons.mpr ⟨child_rejected513_194, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
#print axioms rejected513
theorem rejected514 : ¬ Sat compatible supports domains514 targets514 :=
  refute_empty_domain compatible supports domains514 targets514 13 (by decide)
#print axioms rejected514
theorem rejected515 : ¬ Sat compatible supports domains515 targets515 :=
  refute_empty_domain compatible supports domains515 targets515 13 (by decide)
#print axioms rejected515
theorem rejected516 : ¬ Sat compatible supports domains516 targets516 :=
  refute_empty_domain compatible supports domains516 targets516 4 (by decide)
#print axioms rejected516
theorem rejected517 : ¬ Sat compatible supports domains517 targets517 :=
  refute_empty_domain compatible supports domains517 targets517 10 (by decide)
#print axioms rejected517
set_option maxRecDepth 8192 in
theorem child_rejected518_138 : ¬ Sat compatible supports (childDomains compatible supports domains518 targets518 9 138) (childTargets supports targets518 138) :=
  transport_child domains518 targets518 9 138 domains517 targets517 (by decide) (by decide) rejected517
theorem rejected518 : ¬ Sat compatible supports domains518 targets518 :=
  refute_split compatible supports domains518 targets518 9 [138] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected518_138, List.forall_mem_nil _⟩)
#print axioms rejected518
set_option maxRecDepth 8192 in
theorem child_rejected519_29 : ¬ Sat compatible supports (childDomains compatible supports domains519 targets519 2 29) (childTargets supports targets519 29) :=
  transport_child domains519 targets519 2 29 domains518 targets518 (by decide) (by decide) rejected518
theorem rejected519 : ¬ Sat compatible supports domains519 targets519 :=
  refute_split compatible supports domains519 targets519 2 [29] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected519_29, List.forall_mem_nil _⟩)
#print axioms rejected519
end ElevenSquare.Pending.EncodedSearch
