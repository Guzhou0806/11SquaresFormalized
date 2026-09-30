import ElevenSquare.Pending.S05_Trace
import ElevenSquare.Pending.S06_BaselineCoverCertificate

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Intersect a row with a closed halfplane, retaining its angle interval. -/
def cutRow (h : Halfplane) (r : PoseRow) : PoseRow :=
  { r with centers := h :: r.centers }

def cutRows (h : Halfplane) (rs : List PoseRow) : List PoseRow := rs.map (cutRow h)

def centerCut (s : PoseState) (i : Owner) (h : Halfplane) : PoseState :=
  replaceRows s i (cutRows h (s.rows i))

theorem cutRow_contains (h : Halfplane) (r : PoseRow) (q : UnitSquare) :
    (cutRow h r).contains q ↔ r.contains q ∧ h.contains q.center := by
  constructor
  · rintro ⟨hp, ht⟩
    refine ⟨⟨?_, ht⟩, hp h (by simp [cutRow])⟩
    intro g hg
    exact hp g (by simp [cutRow, hg])
  · rintro ⟨⟨hp, ht⟩, hh⟩
    refine ⟨?_, ht⟩
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hh
    · exact hp g hg

theorem cutRows_contains (h : Halfplane) (rs : List PoseRow) (q : UnitSquare) :
    RowsContain (cutRows h rs) q ↔ RowsContain rs q ∧ h.contains q.center := by
  constructor
  · rintro ⟨r, hr, hq⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    have hc := (cutRow_contains h s q).mp hq
    exact ⟨⟨s, hs, hc.1⟩, hc.2⟩
  · rintro ⟨⟨r, hr, hq⟩, hh⟩
    exact ⟨cutRow h r, List.mem_map.mpr ⟨r, hr, rfl⟩,
      (cutRow_contains h r q).mpr ⟨hq, hh⟩⟩

theorem centerCut_holds {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (h : Halfplane) :
    StateHolds P (centerCut s i h) ↔
      StateHolds P s ∧ h.contains (P.squares i).center := by
  constructor
  · intro hs
    have hi : RowsContain (cutRows h (s.rows i)) (P.squares i) := by
      simpa only [centerCut, replaceRows, Function.update_self] using hs.1 i
    have hc := (cutRows_contains h (s.rows i) (P.squares i)).mp hi
    refine ⟨⟨?_, hs.2⟩, hc.2⟩
    intro j
    by_cases hji : j = i
    · subst j
      exact hc.1
    · simpa only [centerCut, replaceRows, Function.update_of_ne hji] using hs.1 j
  · rintro ⟨hs, hh⟩
    refine ⟨?_, hs.2⟩
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [centerCut, replaceRows, Function.update_self] using
        (cutRows_contains h (s.rows i) (P.squares i)).mpr ⟨hs.1 i, hh⟩
    · simpa only [centerCut, replaceRows, Function.update_of_ne hji] using hs.1 j

/-- Both branches include the cut boundary. -/
theorem closed_halfplane_cases (h : Halfplane) (p : Point) :
    h.contains p ∨ (baselineFlip h).contains p := by
  by_cases hp : h.contains p
  · exact Or.inl hp
  · right
    dsimp [Halfplane.contains, baselineFlip] at hp ⊢
    push_cast
    linarith

theorem centerCut_cover {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (h : Halfplane) (hs : StateHolds P s) :
    StateHolds P (centerCut s i h) ∨
      StateHolds P (centerCut s i (baselineFlip h)) := by
  rcases closed_halfplane_cases h (P.squares i).center with hp | hp
  · exact Or.inl ((centerCut_holds P s i h).mpr ⟨hs, hp⟩)
  · exact Or.inr ((centerCut_holds P s i (baselineFlip h)).mpr ⟨hs, hp⟩)

/-- Finite branch proofs keep all assumptions in their state. A split cannot
establish exclusion until both children have proofs. -/
inductive VerifiedCenterTree : PoseState → Prop
  | terminal {s : PoseState} (ht : Terminal s) : VerifiedCenterTree s
  | trace {s t : PoseState} (ht : VerifiedTrace s t) (rest : VerifiedCenterTree t) :
      VerifiedCenterTree s
  | split {s : PoseState} (i : Owner) (h : Halfplane)
      (left : VerifiedCenterTree (centerCut s i h))
      (right : VerifiedCenterTree (centerCut s i (baselineFlip h))) :
      VerifiedCenterTree s

theorem verified_center_tree_sound {S : ℝ} (P : Packing 11 S) {s : PoseState}
    (tree : VerifiedCenterTree s) : StateHolds P s → False := by
  induction tree with
  | terminal ht => intro hs; exact terminal_contradiction P _ hs ht
  | trace ht rest ih => intro hs; exact ih (verified_trace_sound P hs ht)
  | split i h left right ihl ihr =>
    intro hs
    rcases centerCut_cover P _ i h hs with hl | hr
    · exact ihl hl
    · exact ihr hr

end
end ElevenSquare.Tasks.T01
