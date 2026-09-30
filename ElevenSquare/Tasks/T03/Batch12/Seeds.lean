import ElevenSquare.Tasks.T03.CaseTable
import ElevenSquare.Tasks.T03.Initialization.Library64
import ElevenSquare.Tasks.T03.Initialization.Library08

namespace ElevenSquare.Pending.T03.Batch12.Seed2102
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,6,7,9,10,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2102]! = [1,2,3,4,6,7,9,10,12,13,14] :=
  (CaseTable.slice32 2102 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2102 := by
  unfold caseMask
  have hv : (2102 : Fin 2184).val = 2102 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2102)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 2102)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2102

namespace ElevenSquare.Pending.T03.Batch12.Seed2103
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,6,7,9,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2103]! = [1,2,3,4,6,7,9,11,12,13,14] :=
  (CaseTable.slice32 2103 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2103 := by
  unfold caseMask
  have hv : (2103 : Fin 2184).val = 2103 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2103)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 2103)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2103

namespace ElevenSquare.Pending.T03.Batch12.Seed2111
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,7,8,9,10,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2111]! = [1,2,3,4,7,8,9,10,12,13,14] :=
  (CaseTable.slice32 2111 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2111 := by
  unfold caseMask
  have hv : (2111 : Fin 2184).val = 2111 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2111)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 2111)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2111

namespace ElevenSquare.Pending.T03.Batch12.Seed2112
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,7,8,9,10,11,12]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2112]! = [1,2,3,5,6,7,8,9,10,11,12] :=
  (CaseTable.slice33 2112 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2112 := by
  unfold caseMask
  have hv : (2112 : Fin 2184).val = 2112 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2112)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 2112)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2112

namespace ElevenSquare.Pending.T03.Batch12.Seed2114
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,7,8,9,10,11,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2114]! = [1,2,3,5,6,7,8,9,10,11,14] :=
  (CaseTable.slice33 2114 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2114 := by
  unfold caseMask
  have hv : (2114 : Fin 2184).val = 2114 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2114)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 2114)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2114

namespace ElevenSquare.Pending.T03.Batch12.Seed2116
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,7,8,9,10,12,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2116]! = [1,2,3,5,6,7,8,9,10,12,14] :=
  (CaseTable.slice33 2116 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2116 := by
  unfold caseMask
  have hv : (2116 : Fin 2184).val = 2116 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2116)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 2116)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2116

namespace ElevenSquare.Pending.T03.Batch12.Seed2119
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,7,8,9,11,12,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2119]! = [1,2,3,5,6,7,8,9,11,12,14] :=
  (CaseTable.slice33 2119 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2119 := by
  unfold caseMask
  have hv : (2119 : Fin 2184).val = 2119 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2119)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 2119)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2119

namespace ElevenSquare.Pending.T03.Batch12.Seed2122
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,7,8,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2122]! = [1,2,3,5,6,7,8,10,11,12,13] :=
  (CaseTable.slice33 2122 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2122 := by
  unfold caseMask
  have hv : (2122 : Fin 2184).val = 2122 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2122)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2122)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2122

namespace ElevenSquare.Pending.T03.Batch12.Seed2125
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,7,8,10,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2125]! = [1,2,3,5,6,7,8,10,12,13,14] :=
  (CaseTable.slice33 2125 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2125 := by
  unfold caseMask
  have hv : (2125 : Fin 2184).val = 2125 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2125)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2125)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2125

namespace ElevenSquare.Pending.T03.Batch12.Seed2129
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,7,9,10,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2129]! = [1,2,3,5,6,7,9,10,12,13,14] :=
  (CaseTable.slice33 2129 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2129 := by
  unfold caseMask
  have hv : (2129 : Fin 2184).val = 2129 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2129)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2129)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2129

namespace ElevenSquare.Pending.T03.Batch12.Seed2130
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,8,9,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2130]! = [1,2,3,5,6,8,9,10,11,12,13] :=
  (CaseTable.slice33 2130 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2130 := by
  unfold caseMask
  have hv : (2130 : Fin 2184).val = 2130 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2130)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2130)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2130

namespace ElevenSquare.Pending.T03.Batch12.Seed2132
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,6,8,9,10,11,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2132]! = [1,2,3,5,6,8,9,10,11,13,14] :=
  (CaseTable.slice33 2132 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2132 := by
  unfold caseMask
  have hv : (2132 : Fin 2184).val = 2132 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2132)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2132)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2132

namespace ElevenSquare.Pending.T03.Batch12.Seed2133
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,7,8,9,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2133]! = [1,2,3,5,7,8,9,10,11,12,13] :=
  (CaseTable.slice33 2133 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2133 := by
  unfold caseMask
  have hv : (2133 : Fin 2184).val = 2133 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2133)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2133)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2133

namespace ElevenSquare.Pending.T03.Batch12.Seed2135
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,5,7,8,9,10,11,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2135]! = [1,2,3,5,7,8,9,10,11,13,14] :=
  (CaseTable.slice33 2135 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2135 := by
  unfold caseMask
  have hv : (2135 : Fin 2184).val = 2135 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2135)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2135)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch12.Seed2135
