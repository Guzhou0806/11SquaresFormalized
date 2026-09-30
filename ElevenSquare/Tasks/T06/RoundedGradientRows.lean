import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem roundedGradient_row_00 : roundedGradients 0 = ![1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_01 : roundedGradients 1 = ![1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_02 : roundedGradients 2 = ![0, 1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_03 : roundedGradients 3 = ![0, 1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_04 : roundedGradients 4 = ![0, 0, 0, -1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_05 : roundedGradients 5 = ![0, 0, 0, -1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_06 : roundedGradients 6 = ![0, 0, 0, 0, 1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_07 : roundedGradients 7 = ![0, 0, 0, 0, 1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_08 : roundedGradients 8 = ![0, 0, 0, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_09 : roundedGradients 9 = ![0, 0, 0, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_10 : roundedGradients 10 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_11 : roundedGradients 11 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_12 : roundedGradients 12 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_13 : roundedGradients 13 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_14 : roundedGradients 14 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_15 : roundedGradients 15 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_16 : roundedGradients 16 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_17 : roundedGradients 17 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_18 : roundedGradients 18 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_19 : roundedGradients 19 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 0, -59391303775] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_20 : roundedGradients 20 = ![-763999473636, -645216866087, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 763999473636, 645216866087, 170091401113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_21 : roundedGradients 21 = ![0, 0, 0, 645216866087, -763999473636, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -90783660276, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_22 : roundedGradients 22 = ![0, 0, 0, 0, 0, 0, 763999473636, 645216866087, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 478992826450, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_23 : roundedGradients 23 = ![0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 645216866087, -763999473636, -239124938611] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_24 : roundedGradients 24 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 0, -500000000000, 1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_25 : roundedGradients 25 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 0, 500000000000, 1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_26 : roundedGradients 26 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 500000000000, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_27 : roundedGradients 27 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -500000000000, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_28 : roundedGradients 28 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -500000000000, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_29 : roundedGradients 29 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -1500000000000, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_30 : roundedGradients 30 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 645216866087, -763999473636, -475125464974, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_31 : roundedGradients 31 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 59391303775, 645216866087, -763999473636, -65909125251, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_32 : roundedGradients 32 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 524874535026, 645216866087, -763999473636, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_33 : roundedGradients 33 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -475125464974, 645216866087, -763999473636, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_34 : roundedGradients 34 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -500000000000, 0, 0, 0, 763999473636, 645216866087, 618782607549, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_35 : roundedGradients 35 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 500000000000, 0, 0, 0, 763999473636, 645216866087, -381217392451, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_36 : roundedGradients 36 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -500000000000, 0, 0, 0, 763999473636, 645216866087, 618782607549, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_37 : roundedGradients 37 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 500000000000, 0, 0, 0, 763999473636, 645216866087, -381217392451, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_38 : roundedGradients 38 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 524874535026, 645216866087, -763999473636, -500000000000, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_39 : roundedGradients 39 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -475125464974, 645216866087, -763999473636, 500000000000, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_40 : roundedGradients 40 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -166224039637, 763999473636, 645216866087, 500000000000] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_41 : roundedGradients 41 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 833775960363, 763999473636, 645216866087, -500000000000] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_42 : roundedGradients 42 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 500000000000, 0, -1000000000000, -1500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_43 : roundedGradients 43 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 500000000000, -1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_44 : roundedGradients 44 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, -500000000000, -1000000000000, 0, 1500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_45 : roundedGradients 45 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 1500000000000, -1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_46 : roundedGradients 46 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -500000000000, 763999473636, 645216866087, 833775960363] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_47 : roundedGradients 47 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 500000000000, 763999473636, 645216866087, -166224039637] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_48 : roundedGradients 48 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -500000000000, 645216866087, -763999473636, 524874535026, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_49 : roundedGradients 49 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 500000000000, 645216866087, -763999473636, -475125464974, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_50 : roundedGradients 50 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -381217392451, 0, 0, 0, 763999473636, 645216866087, 500000000000, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_51 : roundedGradients 51 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 618782607549, 0, 0, 0, 763999473636, 645216866087, -500000000000, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_52 : roundedGradients 52 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -500000000000, 645216866087, -763999473636, 524874535026, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_53 : roundedGradients 53 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 500000000000, 645216866087, -763999473636, -475125464974, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_54 : roundedGradients 54 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -381217392451, 0, 0, 0, 763999473636, 645216866087, 500000000000, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
theorem roundedGradient_row_55 : roundedGradients 55 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 618782607549, 0, 0, 0, 763999473636, 645216866087, -500000000000, 0, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl
end ElevenSquare.Tasks.T06
