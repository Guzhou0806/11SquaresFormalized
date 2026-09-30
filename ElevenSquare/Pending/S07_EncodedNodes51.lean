import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes50
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected408_8 : ¬ Sat compatible supports (childDomains compatible supports domains408 targets408 0 8) (childTargets supports targets408 8) :=
  transport_child domains408 targets408 0 8 domains407 targets407 (by decide) (by decide) rejected407
theorem rejected408 : ¬ Sat compatible supports domains408 targets408 :=
  refute_split compatible supports domains408 targets408 0 [8] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected408_8, List.forall_mem_nil _⟩)
#print axioms rejected408
set_option maxRecDepth 8192 in
theorem child_rejected409_25 : ¬ Sat compatible supports (childDomains compatible supports domains409 targets409 2 25) (childTargets supports targets409 25) :=
  transport_child domains409 targets409 2 25 domains408 targets408 (by decide) (by decide) rejected408
theorem rejected409 : ¬ Sat compatible supports domains409 targets409 :=
  refute_split compatible supports domains409 targets409 2 [25] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected409_25, List.forall_mem_nil _⟩)
#print axioms rejected409
theorem rejected410 : ¬ Sat compatible supports domains410 targets410 :=
  refute_empty_domain compatible supports domains410 targets410 2 (by decide)
#print axioms rejected410
theorem rejected411 : ¬ Sat compatible supports domains411 targets411 :=
  refute_empty_domain compatible supports domains411 targets411 2 (by decide)
#print axioms rejected411
set_option maxRecDepth 8192 in
theorem child_rejected412_101 : ¬ Sat compatible supports (childDomains compatible supports domains412 targets412 7 101) (childTargets supports targets412 101) :=
  transport_child domains412 targets412 7 101 domains406 targets406 (by decide) (by decide) rejected406
set_option maxRecDepth 8192 in
theorem child_rejected412_103 : ¬ Sat compatible supports (childDomains compatible supports domains412 targets412 7 103) (childTargets supports targets412 103) :=
  transport_child domains412 targets412 7 103 domains409 targets409 (by decide) (by decide) rejected409
set_option maxRecDepth 8192 in
theorem child_rejected412_104 : ¬ Sat compatible supports (childDomains compatible supports domains412 targets412 7 104) (childTargets supports targets412 104) :=
  transport_child domains412 targets412 7 104 domains410 targets410 (by decide) (by decide) rejected410
set_option maxRecDepth 8192 in
theorem child_rejected412_108 : ¬ Sat compatible supports (childDomains compatible supports domains412 targets412 7 108) (childTargets supports targets412 108) :=
  transport_child domains412 targets412 7 108 domains411 targets411 (by decide) (by decide) rejected411
theorem rejected412 : ¬ Sat compatible supports domains412 targets412 :=
  refute_split compatible supports domains412 targets412 7 [101, 103, 104, 108] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected412_101, (List.forall_mem_cons.mpr ⟨child_rejected412_103, (List.forall_mem_cons.mpr ⟨child_rejected412_104, (List.forall_mem_cons.mpr ⟨child_rejected412_108, List.forall_mem_nil _⟩)⟩)⟩)⟩)
#print axioms rejected412
set_option maxRecDepth 8192 in
theorem child_rejected413_184 : ¬ Sat compatible supports (childDomains compatible supports domains413 targets413 12 184) (childTargets supports targets413 184) :=
  transport_child domains413 targets413 12 184 domains412 targets412 (by decide) (by decide) rejected412
theorem rejected413 : ¬ Sat compatible supports domains413 targets413 :=
  refute_split compatible supports domains413 targets413 12 [184] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected413_184, List.forall_mem_nil _⟩)
#print axioms rejected413
theorem rejected414 : ¬ Sat compatible supports domains414 targets414 :=
  refute_empty_domain compatible supports domains414 targets414 6 (by decide)
#print axioms rejected414
set_option maxRecDepth 8192 in
theorem child_rejected415_179 : ¬ Sat compatible supports (childDomains compatible supports domains415 targets415 11 179) (childTargets supports targets415 179) :=
  transport_child domains415 targets415 11 179 domains414 targets414 (by decide) (by decide) rejected414
theorem rejected415 : ¬ Sat compatible supports domains415 targets415 :=
  refute_split compatible supports domains415 targets415 11 [179] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected415_179, List.forall_mem_nil _⟩)
#print axioms rejected415
end ElevenSquare.Pending.EncodedSearch
