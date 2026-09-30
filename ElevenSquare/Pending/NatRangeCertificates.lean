import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
namespace ElevenSquare.Pending

def AllRange (P : ℕ → Prop) (a n : ℕ) : Prop :=
  ∀ r, a ≤ r → r < a+n → P r

theorem AllRange.of_list {P : ℕ → Prop} {a n : ℕ}
    (h : ∀ r ∈ List.range' a n, P r) : AllRange P a n := by
  intro r hr hs
  exact h r (List.mem_range'_1.mpr ⟨hr, hs⟩)

theorem AllRange.append {P : ℕ → Prop} {a m n : ℕ}
    (hm : AllRange P a m) (hn : AllRange P (a+m) n) : AllRange P a (m+n) := by
  intro r hr hs
  by_cases h : r < a+m
  · exact hm r hr h
  · exact hn r (by omega) (by omega)

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.AllRange.append
