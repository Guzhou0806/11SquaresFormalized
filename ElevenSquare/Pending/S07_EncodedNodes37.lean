import ElevenSquare.Pending.S07_EncodedTransport
import ElevenSquare.Pending.S07_EncodedNodeData
import ElevenSquare.Pending.S07_EncodedNodes36
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
set_option maxRecDepth 8192 in
theorem child_rejected296_70 : ¬ Sat compatible supports (childDomains compatible supports domains296 targets296 5 70) (childTargets supports targets296 70) :=
  transport_child domains296 targets296 5 70 domains295 targets295 (by decide) (by decide) rejected295
theorem rejected296 : ¬ Sat compatible supports domains296 targets296 :=
  refute_split compatible supports domains296 targets296 5 [70] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected296_70, List.forall_mem_nil _⟩)
#print axioms rejected296
theorem rejected297 : ¬ Sat compatible supports domains297 targets297 :=
  refute_empty_domain compatible supports domains297 targets297 5 (by decide)
#print axioms rejected297
set_option maxRecDepth 8192 in
theorem child_rejected298_216 : ¬ Sat compatible supports (childDomains compatible supports domains298 targets298 15 216) (childTargets supports targets298 216) :=
  transport_child domains298 targets298 15 216 domains296 targets296 (by decide) (by decide) rejected296
set_option maxRecDepth 8192 in
theorem child_rejected298_217 : ¬ Sat compatible supports (childDomains compatible supports domains298 targets298 15 217) (childTargets supports targets298 217) :=
  transport_child domains298 targets298 15 217 domains297 targets297 (by decide) (by decide) rejected297
theorem rejected298 : ¬ Sat compatible supports domains298 targets298 :=
  refute_split compatible supports domains298 targets298 15 [216, 217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected298_216, (List.forall_mem_cons.mpr ⟨child_rejected298_217, List.forall_mem_nil _⟩)⟩)
#print axioms rejected298
theorem rejected299 : ¬ Sat compatible supports domains299 targets299 :=
  refute_empty_domain compatible supports domains299 targets299 5 (by decide)
#print axioms rejected299
set_option maxRecDepth 8192 in
theorem child_rejected300_2 : ¬ Sat compatible supports (childDomains compatible supports domains300 targets300 0 2) (childTargets supports targets300 2) :=
  transport_child domains300 targets300 0 2 domains290 targets290 (by decide) (by decide) rejected290
set_option maxRecDepth 8192 in
theorem child_rejected300_4 : ¬ Sat compatible supports (childDomains compatible supports domains300 targets300 0 4) (childTargets supports targets300 4) :=
  transport_child domains300 targets300 0 4 domains291 targets291 (by decide) (by decide) rejected291
set_option maxRecDepth 8192 in
theorem child_rejected300_5 : ¬ Sat compatible supports (childDomains compatible supports domains300 targets300 0 5) (childTargets supports targets300 5) :=
  transport_child domains300 targets300 0 5 domains292 targets292 (by decide) (by decide) rejected292
set_option maxRecDepth 8192 in
theorem child_rejected300_6 : ¬ Sat compatible supports (childDomains compatible supports domains300 targets300 0 6) (childTargets supports targets300 6) :=
  transport_child domains300 targets300 0 6 domains293 targets293 (by decide) (by decide) rejected293
set_option maxRecDepth 8192 in
theorem child_rejected300_7 : ¬ Sat compatible supports (childDomains compatible supports domains300 targets300 0 7) (childTargets supports targets300 7) :=
  transport_child domains300 targets300 0 7 domains294 targets294 (by decide) (by decide) rejected294
set_option maxRecDepth 8192 in
theorem child_rejected300_8 : ¬ Sat compatible supports (childDomains compatible supports domains300 targets300 0 8) (childTargets supports targets300 8) :=
  transport_child domains300 targets300 0 8 domains298 targets298 (by decide) (by decide) rejected298
set_option maxRecDepth 8192 in
theorem child_rejected300_9 : ¬ Sat compatible supports (childDomains compatible supports domains300 targets300 0 9) (childTargets supports targets300 9) :=
  transport_child domains300 targets300 0 9 domains299 targets299 (by decide) (by decide) rejected299
theorem rejected300 : ¬ Sat compatible supports domains300 targets300 :=
  refute_split compatible supports domains300 targets300 0 [2, 4, 5, 6, 7, 8, 9] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected300_2, (List.forall_mem_cons.mpr ⟨child_rejected300_4, (List.forall_mem_cons.mpr ⟨child_rejected300_5, (List.forall_mem_cons.mpr ⟨child_rejected300_6, (List.forall_mem_cons.mpr ⟨child_rejected300_7, (List.forall_mem_cons.mpr ⟨child_rejected300_8, (List.forall_mem_cons.mpr ⟨child_rejected300_9, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms rejected300
theorem rejected301 : ¬ Sat compatible supports domains301 targets301 :=
  refute_empty_domain compatible supports domains301 targets301 13 (by decide)
#print axioms rejected301
set_option maxRecDepth 8192 in
theorem child_rejected302_205 : ¬ Sat compatible supports (childDomains compatible supports domains302 targets302 14 205) (childTargets supports targets302 205) :=
  transport_child domains302 targets302 14 205 domains301 targets301 (by decide) (by decide) rejected301
theorem rejected302 : ¬ Sat compatible supports domains302 targets302 :=
  refute_split compatible supports domains302 targets302 14 [205] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected302_205, List.forall_mem_nil _⟩)
#print axioms rejected302
set_option maxRecDepth 8192 in
theorem child_rejected303_217 : ¬ Sat compatible supports (childDomains compatible supports domains303 targets303 15 217) (childTargets supports targets303 217) :=
  transport_child domains303 targets303 15 217 domains302 targets302 (by decide) (by decide) rejected302
theorem rejected303 : ¬ Sat compatible supports domains303 targets303 :=
  refute_split compatible supports domains303 targets303 15 [217] (by decide) (List.forall_mem_cons.mpr ⟨child_rejected303_217, List.forall_mem_nil _⟩)
#print axioms rejected303
end ElevenSquare.Pending.EncodedSearch
