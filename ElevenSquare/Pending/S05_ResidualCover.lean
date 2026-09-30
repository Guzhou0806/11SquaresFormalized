import ElevenSquare.Pending.Types
import Mathlib.Tactic.Linarith

/-! Closed subdivisions retain their boundary points. Checkpoint: docs/FORMALIZATION_PROGRESS.md. -/

namespace ElevenSquare.Pending
noncomputable section

-- Closed halves overlap on the cut line, including segments and singleton regions.
theorem polygon_closed_split (P : Polygon) (l : Halfplane) :
    P.carrier =
      Polygon.carrier (l :: P) ∪
      Polygon.carrier ((⟨-l.a, -l.b, -l.c⟩ : Halfplane) :: P) := by
  ext p
  simp only [Polygon.carrier, Set.mem_setOf_eq, Set.mem_union, List.mem_cons,
    forall_eq_or_imp]
  constructor
  · intro hp
    rcases le_total ((l.a : ℝ)*p.1 + (l.b : ℝ)*p.2) (l.c : ℝ) with h | h
    · exact Or.inl ⟨h, hp⟩
    · right
      refine ⟨?_, hp⟩
      dsimp [Halfplane.contains]
      push_cast
      linarith
  · rintro (⟨_, hp⟩ | ⟨_, hp⟩) <;> exact hp

theorem angle_closed_split (r : PoseRow) (m : ℚ)
    (hm : r.lo ≤ m ∧ m ≤ r.hi) (q : UnitSquare) :
    r.contains q ↔
      ({r with hi := m} : PoseRow).contains q ∨
      ({r with lo := m} : PoseRow).contains q := by
  constructor
  · rintro ⟨hc, t, h0, h1, hlo, hhi, ha⟩
    rcases le_total t (m : ℝ) with h | h
    · exact Or.inl ⟨hc, t, h0, h1, hlo, h, ha⟩
    · exact Or.inr ⟨hc, t, h0, h1, h, hhi, ha⟩
  · rintro (⟨hc, t, h0, h1, hlo, hhi, ha⟩ | ⟨hc, t, h0, h1, hlo, hhi, ha⟩)
    · exact ⟨hc, t, h0, h1, hlo, hhi.trans (by exact_mod_cast hm.2), ha⟩
    · exact ⟨hc, t, h0, h1, le_trans (by exact_mod_cast hm.1) hlo, hhi, ha⟩

-- Finite subdivision with individually checked leaves; no positive-area hypothesis.
theorem finite_residual_cover
    (old forbidden : Set Point) (pieces kept : List (Set Point))
    (hpieces : old ⊆ ⋃ P ∈ pieces, P)
    (hleaves : ∀ P ∈ pieces, P ⊆ forbidden ∨ ∃ K ∈ kept, P ⊆ K) :
    old ⊆ forbidden ∪ ⋃ K ∈ kept, K := by
  intro p hp
  have hc := hpieces hp
  simp only [Set.mem_iUnion] at hc
  rcases hc with ⟨piece, hpiece, hmem⟩
  rcases hleaves piece hpiece with hbad | ⟨good, hgood, hsub⟩
  · exact Or.inl (hbad hmem)
  · right
    simp only [Set.mem_iUnion]
    exact ⟨good, hgood, hsub hmem⟩


end
end ElevenSquare.Pending
