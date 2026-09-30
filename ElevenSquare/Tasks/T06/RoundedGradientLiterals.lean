import ElevenSquare.Tasks.T06.RoundedGradientRows

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def roundedGradientLiteral00 : Fin 33 → ℤ := ![1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral00_eq : roundedGradients 0 = roundedGradientLiteral00 := roundedGradient_row_00

def roundedGradientLiteral01 : Fin 33 → ℤ := ![1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral01_eq : roundedGradients 1 = roundedGradientLiteral01 := roundedGradient_row_01

def roundedGradientLiteral02 : Fin 33 → ℤ := ![0, 1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral02_eq : roundedGradients 2 = roundedGradientLiteral02 := roundedGradient_row_02

def roundedGradientLiteral03 : Fin 33 → ℤ := ![0, 1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral03_eq : roundedGradients 3 = roundedGradientLiteral03 := roundedGradient_row_03

def roundedGradientLiteral04 : Fin 33 → ℤ := ![0, 0, 0, -1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral04_eq : roundedGradients 4 = roundedGradientLiteral04 := roundedGradient_row_04

def roundedGradientLiteral05 : Fin 33 → ℤ := ![0, 0, 0, -1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral05_eq : roundedGradients 5 = roundedGradientLiteral05 := roundedGradient_row_05

def roundedGradientLiteral06 : Fin 33 → ℤ := ![0, 0, 0, 0, 1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral06_eq : roundedGradients 6 = roundedGradientLiteral06 := roundedGradient_row_06

def roundedGradientLiteral07 : Fin 33 → ℤ := ![0, 0, 0, 0, 1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral07_eq : roundedGradients 7 = roundedGradientLiteral07 := roundedGradient_row_07

def roundedGradientLiteral08 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral08_eq : roundedGradients 8 = roundedGradientLiteral08 := roundedGradient_row_08

def roundedGradientLiteral09 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral09_eq : roundedGradients 9 = roundedGradientLiteral09 := roundedGradient_row_09

def roundedGradientLiteral10 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral10_eq : roundedGradients 10 = roundedGradientLiteral10 := roundedGradient_row_10

def roundedGradientLiteral11 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral11_eq : roundedGradients 11 = roundedGradientLiteral11 := roundedGradient_row_11

def roundedGradientLiteral12 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral12_eq : roundedGradients 12 = roundedGradientLiteral12 := roundedGradient_row_12

def roundedGradientLiteral13 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral13_eq : roundedGradients 13 = roundedGradientLiteral13 := roundedGradient_row_13

def roundedGradientLiteral14 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral14_eq : roundedGradients 14 = roundedGradientLiteral14 := roundedGradient_row_14

def roundedGradientLiteral15 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral15_eq : roundedGradients 15 = roundedGradientLiteral15 := roundedGradient_row_15

def roundedGradientLiteral16 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral16_eq : roundedGradients 16 = roundedGradientLiteral16 := roundedGradient_row_16

def roundedGradientLiteral17 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral17_eq : roundedGradients 17 = roundedGradientLiteral17 := roundedGradient_row_17

def roundedGradientLiteral18 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral18_eq : roundedGradients 18 = roundedGradientLiteral18 := roundedGradient_row_18

def roundedGradientLiteral19 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 0, -59391303775]

theorem roundedGradientLiteral19_eq : roundedGradients 19 = roundedGradientLiteral19 := roundedGradient_row_19

def roundedGradientLiteral20 : Fin 33 → ℤ := ![-763999473636, -645216866087, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 763999473636, 645216866087, 170091401113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral20_eq : roundedGradients 20 = roundedGradientLiteral20 := roundedGradient_row_20

def roundedGradientLiteral21 : Fin 33 → ℤ := ![0, 0, 0, 645216866087, -763999473636, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -90783660276, 0, 0, 0]

theorem roundedGradientLiteral21_eq : roundedGradients 21 = roundedGradientLiteral21 := roundedGradient_row_21

def roundedGradientLiteral22 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 763999473636, 645216866087, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 478992826450, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral22_eq : roundedGradients 22 = roundedGradientLiteral22 := roundedGradient_row_22

def roundedGradientLiteral23 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 645216866087, -763999473636, -239124938611]

theorem roundedGradientLiteral23_eq : roundedGradients 23 = roundedGradientLiteral23 := roundedGradient_row_23

def roundedGradientLiteral24 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 0, -500000000000, 1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral24_eq : roundedGradients 24 = roundedGradientLiteral24 := roundedGradient_row_24

def roundedGradientLiteral25 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1000000000000, 0, 500000000000, 1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral25_eq : roundedGradients 25 = roundedGradientLiteral25 := roundedGradient_row_25

def roundedGradientLiteral26 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 500000000000, 0, 0, 0, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral26_eq : roundedGradients 26 = roundedGradientLiteral26 := roundedGradient_row_26

def roundedGradientLiteral27 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -500000000000, 0, 0, 0, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral27_eq : roundedGradients 27 = roundedGradientLiteral27 := roundedGradient_row_27

def roundedGradientLiteral28 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -500000000000, 0, -1000000000000, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral28_eq : roundedGradients 28 = roundedGradientLiteral28 := roundedGradient_row_28

def roundedGradientLiteral29 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, -1500000000000, 0, -1000000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral29_eq : roundedGradients 29 = roundedGradientLiteral29 := roundedGradient_row_29

def roundedGradientLiteral30 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 59391303775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 645216866087, -763999473636, -475125464974, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral30_eq : roundedGradients 30 = roundedGradientLiteral30 := roundedGradient_row_30

def roundedGradientLiteral31 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 59391303775, 645216866087, -763999473636, -65909125251, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral31_eq : roundedGradients 31 = roundedGradientLiteral31 := roundedGradient_row_31

def roundedGradientLiteral32 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 524874535026, 645216866087, -763999473636, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral32_eq : roundedGradients 32 = roundedGradientLiteral32 := roundedGradient_row_32

def roundedGradientLiteral33 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -475125464974, 645216866087, -763999473636, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral33_eq : roundedGradients 33 = roundedGradientLiteral33 := roundedGradient_row_33

def roundedGradientLiteral34 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -500000000000, 0, 0, 0, 763999473636, 645216866087, 618782607549, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral34_eq : roundedGradients 34 = roundedGradientLiteral34 := roundedGradient_row_34

def roundedGradientLiteral35 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 500000000000, 0, 0, 0, 763999473636, 645216866087, -381217392451, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral35_eq : roundedGradients 35 = roundedGradientLiteral35 := roundedGradient_row_35

def roundedGradientLiteral36 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -500000000000, 0, 0, 0, 763999473636, 645216866087, 618782607549, 0, 0, 0]

theorem roundedGradientLiteral36_eq : roundedGradients 36 = roundedGradientLiteral36 := roundedGradient_row_36

def roundedGradientLiteral37 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 500000000000, 0, 0, 0, 763999473636, 645216866087, -381217392451, 0, 0, 0]

theorem roundedGradientLiteral37_eq : roundedGradients 37 = roundedGradientLiteral37 := roundedGradient_row_37

def roundedGradientLiteral38 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 524874535026, 645216866087, -763999473636, -500000000000, 0, 0, 0]

theorem roundedGradientLiteral38_eq : roundedGradients 38 = roundedGradientLiteral38 := roundedGradient_row_38

def roundedGradientLiteral39 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -475125464974, 645216866087, -763999473636, 500000000000, 0, 0, 0]

theorem roundedGradientLiteral39_eq : roundedGradients 39 = roundedGradientLiteral39 := roundedGradient_row_39

def roundedGradientLiteral40 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -166224039637, 763999473636, 645216866087, 500000000000]

theorem roundedGradientLiteral40_eq : roundedGradients 40 = roundedGradientLiteral40 := roundedGradient_row_40

def roundedGradientLiteral41 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 833775960363, 763999473636, 645216866087, -500000000000]

theorem roundedGradientLiteral41_eq : roundedGradients 41 = roundedGradientLiteral41 := roundedGradient_row_41

def roundedGradientLiteral42 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 500000000000, 0, -1000000000000, -1500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral42_eq : roundedGradients 42 = roundedGradientLiteral42 := roundedGradient_row_42

def roundedGradientLiteral43 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 500000000000, -1000000000000, 0, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral43_eq : roundedGradients 43 = roundedGradientLiteral43 := roundedGradient_row_43

def roundedGradientLiteral44 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, -500000000000, -1000000000000, 0, 1500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral44_eq : roundedGradients 44 = roundedGradientLiteral44 := roundedGradient_row_44

def roundedGradientLiteral45 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000000000000, 0, 1500000000000, -1000000000000, 0, -500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral45_eq : roundedGradients 45 = roundedGradientLiteral45 := roundedGradient_row_45

def roundedGradientLiteral46 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -500000000000, 763999473636, 645216866087, 833775960363]

theorem roundedGradientLiteral46_eq : roundedGradients 46 = roundedGradientLiteral46 := roundedGradient_row_46

def roundedGradientLiteral47 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 500000000000, 763999473636, 645216866087, -166224039637]

theorem roundedGradientLiteral47_eq : roundedGradients 47 = roundedGradientLiteral47 := roundedGradient_row_47

def roundedGradientLiteral48 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -500000000000, 645216866087, -763999473636, 524874535026, 0, 0, 0]

theorem roundedGradientLiteral48_eq : roundedGradients 48 = roundedGradientLiteral48 := roundedGradient_row_48

def roundedGradientLiteral49 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 500000000000, 645216866087, -763999473636, -475125464974, 0, 0, 0]

theorem roundedGradientLiteral49_eq : roundedGradients 49 = roundedGradientLiteral49 := roundedGradient_row_49

def roundedGradientLiteral50 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -381217392451, 0, 0, 0, 763999473636, 645216866087, 500000000000, 0, 0, 0]

theorem roundedGradientLiteral50_eq : roundedGradients 50 = roundedGradientLiteral50 := roundedGradient_row_50

def roundedGradientLiteral51 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 618782607549, 0, 0, 0, 763999473636, 645216866087, -500000000000, 0, 0, 0]

theorem roundedGradientLiteral51_eq : roundedGradients 51 = roundedGradientLiteral51 := roundedGradient_row_51

def roundedGradientLiteral52 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, -500000000000, 645216866087, -763999473636, 524874535026, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral52_eq : roundedGradients 52 = roundedGradientLiteral52 := roundedGradient_row_52

def roundedGradientLiteral53 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -645216866087, 763999473636, 500000000000, 645216866087, -763999473636, -475125464974, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral53_eq : roundedGradients 53 = roundedGradientLiteral53 := roundedGradient_row_53

def roundedGradientLiteral54 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, -381217392451, 0, 0, 0, 763999473636, 645216866087, 500000000000, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral54_eq : roundedGradients 54 = roundedGradientLiteral54 := roundedGradient_row_54

def roundedGradientLiteral55 : Fin 33 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -763999473636, -645216866087, 618782607549, 0, 0, 0, 763999473636, 645216866087, -500000000000, 0, 0, 0, 0, 0, 0]

theorem roundedGradientLiteral55_eq : roundedGradients 55 = roundedGradientLiteral55 := roundedGradient_row_55

end ElevenSquare.Tasks.T06
