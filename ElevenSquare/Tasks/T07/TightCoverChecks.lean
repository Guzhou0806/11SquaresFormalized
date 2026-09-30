import ElevenSquare.CoverChecks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-! Independent, tighter rational dyadic covering radius for the physical-site diamond. -/
namespace ElevenSquare

def TightBoxCovered (x y h : ℝ) : Prop :=
  ∀ (p : ℝ × ℝ), x ≤ p.1 → p.1 ≤ x+h → y ≤ p.2 → p.2 ≤ y+h →
    ∃ i : Fin 16, coordinateDistanceSq p (coverSite i) ≤ (17 / 100 : ℝ)^2

theorem tightBoxCovered_split (x y h : ℝ)
    (h00 : TightBoxCovered x y (h/2))
    (h10 : TightBoxCovered (x+h/2) y (h/2))
    (h01 : TightBoxCovered x (y+h/2) (h/2))
    (h11 : TightBoxCovered (x+h/2) (y+h/2) (h/2)) : TightBoxCovered x y h := by
  intro p hxl hxu hyl hyu
  by_cases hx : p.1 ≤ x+h/2
  · by_cases hy : p.2 ≤ y+h/2
    · exact h00 p hxl hx hyl hy
    · exact h01 p hxl hx (le_of_lt (lt_of_not_ge hy)) (by linarith)
  · by_cases hy : p.2 ≤ y+h/2
    · exact h10 p (le_of_lt (lt_of_not_ge hx)) (by linarith) hyl hy
    · exact h11 p (le_of_lt (lt_of_not_ge hx)) (by linarith)
        (le_of_lt (lt_of_not_ge hy)) (by linarith)

theorem tightBoxCovered_leaf (x y h a b mx my : ℝ) (i : Fin 16)
    (hs : coverSite i = (a,b))
    (hx0 : a - mx ≤ x) (hx1 : x+h ≤ a+mx)
    (hy0 : b - my ≤ y) (hy1 : y+h ≤ b+my)
    (hr : mx^2+my^2 ≤ (17 / 100 : ℝ)^2) : TightBoxCovered x y h := by
  intro p hxl hxu hyl hyu
  refine ⟨i, ?_⟩
  rw [hs]
  have hx : (p.1-a)^2 ≤ mx^2 := sq_le_sq' (by linarith) (by linarith)
  have hy : (p.2-b)^2 ≤ my^2 := sq_le_sq' (by linarith) (by linarith)
  exact le_trans (add_le_add hx hy) hr

end ElevenSquare
