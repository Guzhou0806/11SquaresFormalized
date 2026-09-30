import ElevenSquare.Tasks.T06.Data

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending

def coordinateRadiiQ : Fin 33 → ℚ :=
  ![(18767167 / 10000000000), (4435327 / 2000000000), (5670363 / 2500000000), (1636033 / 1000000000), (6880181 / 5000000000), (1764113 / 1000000000), (8962451 / 10000000000), (5212397 / 5000000000), (5670363 / 2500000000), (1635053 / 1000000000), (10683139 / 10000000000), (1890121 / 1250000000), (4087019 / 2500000000), (13962901 / 10000000000), (20161291 / 10000000000), (12900283 / 10000000000), (534153 / 500000000), (1890121 / 1250000000), (678279 / 500000000), (4124329 / 5000000000), (35312013 / 10000000000), (11182451 / 10000000000), (3232837 / 5000000000), (8824483 / 2500000000), (9356857 / 10000000000), (8671199 / 10000000000), (7549783 / 5000000000), (293551 / 400000000), (10335557 / 10000000000), (40352153 / 10000000000), (1920157 / 2500000000), (8222903 / 2500000000), (67647473 / 10000000000)]

def maxRadiusQ : ℚ := (67647473 / 10000000000)

def certificateWeight (nums : Fin 42 → ℕ) (i : Fin 42) : ℚ :=
  (nums i : ℚ) / 1000000000000

def certificateMatrix (b : Fin 128) (i : Fin 42) (k : Fin 33) : ℚ :=
  (roundedGradients (branchRows b i) k : ℚ) / 1000000000000

def certificateResidualCheck (b : Fin 128) (j : Fin 33) (s : Fin 2)
    (nums : Fin 42 → ℕ) (eps : ℚ) : Prop :=
  (∑ k : Fin 33, |(∑ i : Fin 42, certificateWeight nums i * certificateMatrix b i k) -
      (if k = j then (![-1, 1] : Fin 2 → ℚ) s else 0)|) +
      33 * (1 / 1000000000000 : ℚ) * (∑ i : Fin 42, certificateWeight nums i) ≤ eps

def certificateMassCheck (b : Fin 128) (j : Fin 33)
    (nums : Fin 42 → ℕ) (eps : ℚ) : Prop :=
  (∑ i : Fin 42, certificateWeight nums i * rowCurvatures (branchRows b i)) <
    2 * (coordinateRadiiQ j - eps * maxRadiusQ)

instance (b : Fin 128) (j : Fin 33) (s : Fin 2) (nums : Fin 42 → ℕ) (eps : ℚ) :
    Decidable (certificateResidualCheck b j s nums eps) := by
  unfold certificateResidualCheck
  infer_instance

instance (b : Fin 128) (j : Fin 33) (nums : Fin 42 → ℕ) (eps : ℚ) :
    Decidable (certificateMassCheck b j nums eps) := by
  unfold certificateMassCheck
  infer_instance

end ElevenSquare.Tasks.T06
