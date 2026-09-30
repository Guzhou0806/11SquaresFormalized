import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes29
import ElevenSquare.Pending.S07_EncodedNodes42
import ElevenSquare.Pending.S07_EncodedNodes45
import ElevenSquare.Pending.S07_EncodedNodes48
import ElevenSquare.Pending.S07_EncodedNodes49
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
theorem rejected400 : ¬ Sat compatible supports domains400 targets400 :=
  refute_empty_domain compatible supports domains400 targets400 0 (by decide)
#print axioms rejected400
theorem rejected401 : ¬ Sat compatible supports domains401 targets401 :=
  refute_empty_domain compatible supports domains401 targets401 5 (by decide)
#print axioms rejected401
set_option maxRecDepth 8192 in
theorem child_rejected402_13 : ¬ Sat compatible supports (childDomains compatible supports domains402 targets402 1 13) (childTargets supports targets402 13) :=
  transport_child domains402 targets402 1 13 domains400 targets400 (by decide) (by decide) rejected400
set_option maxRecDepth 8192 in
theorem child_rejected402_17 : ¬ Sat compatible supports (childDomains compatible supports domains402 targets402 1 17) (childTargets supports targets402 17) :=
  transport_child domains402 targets402 1 17 domains401 targets401 (by decide) (by decide) rejected401
theorem rejected402 : ¬ Sat compatible supports domains402 targets402 :=
  refute_split compatible supports domains402 targets402 1 [13, 17] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected402_13, (List.forall_mem_cons.mpr ⟨child_rejected402_17, List.forall_mem_nil _⟩)⟩)
#print axioms rejected402
set_option maxRecDepth 8192 in
theorem child_rejected403_201 : ¬ Sat compatible supports (childDomains compatible supports domains403 targets403 14 201) (childTargets supports targets403 201) :=
  transport_child domains403 targets403 14 201 domains402 targets402 (by decide) (by decide) rejected402
theorem rejected403 : ¬ Sat compatible supports domains403 targets403 :=
  refute_split compatible supports domains403 targets403 14 [201] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected403_201, List.forall_mem_nil _⟩)
#print axioms rejected403
set_option maxRecDepth 8192 in
theorem child_rejected404_194 : ¬ Sat compatible supports (childDomains compatible supports domains404 targets404 13 194) (childTargets supports targets404 194) :=
  transport_child domains404 targets404 13 194 domains399 targets399 (by decide) (by decide) rejected399
set_option maxRecDepth 8192 in
theorem child_rejected404_197 : ¬ Sat compatible supports (childDomains compatible supports domains404 targets404 13 197) (childTargets supports targets404 197) :=
  transport_child domains404 targets404 13 197 domains403 targets403 (by decide) (by decide) rejected403
theorem rejected404 : ¬ Sat compatible supports domains404 targets404 :=
  refute_split compatible supports domains404 targets404 13 [194, 197] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected404_194, (List.forall_mem_cons.mpr ⟨child_rejected404_197, List.forall_mem_nil _⟩)⟩)
#print axioms rejected404
set_option maxRecDepth 8192 in
theorem child_rejected405_34 : ¬ Sat compatible supports (childDomains compatible supports domains405 targets405 3 34) (childTargets supports targets405 34) :=
  transport_child domains405 targets405 3 34 domains239 targets239 (by decide) (by decide) rejected239
set_option maxRecDepth 8192 in
theorem child_rejected405_35 : ¬ Sat compatible supports (childDomains compatible supports domains405 targets405 3 35) (childTargets supports targets405 35) :=
  transport_child domains405 targets405 3 35 domains337 targets337 (by decide) (by decide) rejected337
set_option maxRecDepth 8192 in
theorem child_rejected405_36 : ¬ Sat compatible supports (childDomains compatible supports domains405 targets405 3 36) (childTargets supports targets405 36) :=
  transport_child domains405 targets405 3 36 domains362 targets362 (by decide) (by decide) rejected362
set_option maxRecDepth 8192 in
theorem child_rejected405_37 : ¬ Sat compatible supports (childDomains compatible supports domains405 targets405 3 37) (childTargets supports targets405 37) :=
  transport_child domains405 targets405 3 37 domains386 targets386 (by decide) (by decide) rejected386
set_option maxRecDepth 8192 in
theorem child_rejected405_38 : ¬ Sat compatible supports (childDomains compatible supports domains405 targets405 3 38) (childTargets supports targets405 38) :=
  transport_child domains405 targets405 3 38 domains395 targets395 (by decide) (by decide) rejected395
set_option maxRecDepth 8192 in
theorem child_rejected405_39 : ¬ Sat compatible supports (childDomains compatible supports domains405 targets405 3 39) (childTargets supports targets405 39) :=
  transport_child domains405 targets405 3 39 domains404 targets404 (by decide) (by decide) rejected404
theorem rejected405 : ¬ Sat compatible supports domains405 targets405 :=
  refute_split compatible supports domains405 targets405 3 [34, 35, 36, 37, 38, 39] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected405_34, (List.forall_mem_cons.mpr ⟨child_rejected405_35, (List.forall_mem_cons.mpr ⟨child_rejected405_36, (List.forall_mem_cons.mpr ⟨child_rejected405_37, (List.forall_mem_cons.mpr ⟨child_rejected405_38, (List.forall_mem_cons.mpr ⟨child_rejected405_39, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected405
theorem rejected406 : ¬ Sat compatible supports domains406 targets406 :=
  refute_empty_domain compatible supports domains406 targets406 2 (by decide)
#print axioms rejected406
theorem rejected407 : ¬ Sat compatible supports domains407 targets407 :=
  refute_empty_domain compatible supports domains407 targets407 4 (by decide)
#print axioms rejected407
end ElevenSquare.Pending.EncodedSearch
