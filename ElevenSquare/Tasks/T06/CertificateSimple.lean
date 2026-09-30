import ElevenSquare.Tasks.T06.DataIntegral

namespace ElevenSquare.Tasks.T06

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def simpleIntegerCheck (dots : Fin 33 → (Fin 42 → ℕ) → ℤ)
    (K : Fin 42 → ℕ) (j : Fin 33) (s : Fin 2) (n : Fin 42 → ℕ) (E R : ℕ) : Prop :=
  ((∑ k : Fin 33, |dots k n - (if k = j then (![-1, 1] : Fin 2 → ℤ) s *
      1000000000000000000000000 else 0)|) + 33 * (∑ i : Fin 42, (n i : ℤ)) ≤ (E : ℤ)) ∧
  ((∑ i : Fin 42, n i * K i) * 10000000000 + 2 * E * 67647473 <
      2 * R * 1000000000000000000000000)

instance (dots : Fin 33 → (Fin 42 → ℕ) → ℤ) (K : Fin 42 → ℕ)
    (j : Fin 33) (s : Fin 2) (n : Fin 42 → ℕ) (E R : ℕ) :
    Decidable (simpleIntegerCheck dots K j s n E R) := by
  unfold simpleIntegerCheck
  infer_instance

theorem integerChecks_of_simple (b : Fin 128) (j : Fin 33) (s : Fin 2)
    (nums n : Fin 42 → ℕ) (E R : ℕ)
    (dots : Fin 33 → (Fin 42 → ℕ) → ℤ) (K : Fin 42 → ℕ)
    (hdots : ∀ (n : Fin 42 → ℕ) (k : Fin 33),
      (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows b i) k) = dots k n)
    (hK : ∀ i : Fin 42, curvatureNumerators (branchRows b i) = K i)
    (hn : nums = n) (he : residualNumerators b j s = E) (hr : radiusNumerators j = R)
    (hc : simpleIntegerCheck dots K j s n E R) :
    integerResidualCheck b j s nums ∧ integerMassCheck b j s nums := by
  constructor
  · unfold integerResidualCheck
    simp_rw [hdots]
    rw [hn, he]
    exact hc.1
  · unfold integerMassCheck
    simp_rw [hK]
    rw [hn, he, hr]
    exact hc.2

end ElevenSquare.Tasks.T06
