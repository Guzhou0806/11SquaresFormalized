import ElevenSquare.Tasks.T01.Field03Feature

namespace ElevenSquare.Tasks.T01
noncomputable section

/-- Each closed interval starts before the preceding covered endpoint. -/
def ClosedWindowChain : ℚ → List (ℚ × ℚ) → Prop
  | frontier, [] => 1 ≤ frontier
  | frontier, w :: ws => w.1 ≤ frontier ∧ ClosedWindowChain w.2 ws

/-- A finite closed chain starts at zero and reaches one. -/
def ClosedWindowCoverCheck : List (ℚ × ℚ) → Prop
  | [] => False
  | w :: ws => w.1 ≤ 0 ∧ ClosedWindowChain w.2 ws

private theorem closed_window_chain_sound (M : ℝ → Prop)
    (frontier : ℚ) (windows : List (ℚ × ℚ))
    (hc : ClosedWindowChain frontier windows)
    (hp : ∀ t : ℝ, 0 ≤ t → t ≤ (frontier : ℝ) → M t)
    (hr : ∀ w ∈ windows, ∀ t : ℝ, (w.1 : ℝ) ≤ t → t ≤ (w.2 : ℝ) → M t) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → M t := by
  induction windows generalizing frontier with
  | nil =>
      intro t ht0 ht1
      exact hp t ht0 (ht1.trans (by exact_mod_cast hc))
  | cons w ws ih =>
      apply ih w.2 hc.2
      · intro t ht0 hthi
        by_cases htf : t ≤ (frontier : ℝ)
        · exact hp t ht0 htf
        · exact hr w (List.mem_cons_self) t
            ((by exact_mod_cast hc.1 : (w.1 : ℝ) ≤ (frontier : ℝ)).trans
              (le_of_lt (lt_of_not_ge htf))) hthi
      · intro v hv
        exact hr v (List.mem_cons_of_mem w hv)

/-- The finite rational endpoint check proves coverage, including every boundary. -/
theorem closed_window_cover_sound (windows : List (ℚ × ℚ))
    (hc : ClosedWindowCoverCheck windows) (M : ℝ → Prop)
    (hr : ∀ w ∈ windows, ∀ t : ℝ, (w.1 : ℝ) ≤ t → t ≤ (w.2 : ℝ) → M t)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : M t := by
  cases windows with
  | nil => exact hc.elim
  | cons w ws =>
      apply closed_window_chain_sound M w.2 ws hc.2 ?_ ?_ t ht0 ht1
      · intro u hu0 huu
        exact hr w (List.mem_cons_self) u
          ((by exact_mod_cast hc.1 : (w.1 : ℝ) ≤ 0).trans hu0) huu
      · intro v hv
        exact hr v (List.mem_cons_of_mem w hv)

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.closed_window_cover_sound
