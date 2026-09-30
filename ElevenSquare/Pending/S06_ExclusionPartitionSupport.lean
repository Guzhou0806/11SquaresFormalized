import ElevenSquare.Pending.S06_ExclusionCounts
import ElevenSquare.Pending.SortedDisjoint
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData

theorem candidate_block : Block id candidateArray.toList 4 438 1659 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩

theorem bounded_sound (xs : List ℕ) (n : ℕ)
    (h : xs.all (fun x => decide (x < n)) = true) : ∀ x ∈ xs, x < n := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

def BaselineGood (xs : Array ℕ) : Prop :=
  (∀ x ∈ xs.toList, x < 2184) ∧ xs.toList.Disjoint priorArray.toList ∧
    xs.toList.Disjoint returnedArray.toList ∧ xs.toList.Disjoint candidateArray.toList

theorem BaselineGood.append {xs ys : Array ℕ} (hx : BaselineGood xs) (hy : BaselineGood ys) :
    BaselineGood (xs ++ ys) := by
  constructor
  · intro x h
    rw [array_toList_append, List.mem_append] at h
    exact h.elim (hx.1 x) (hy.1 x)
  · refine ⟨?_, ?_, ?_⟩
    · intro x h hp
      rw [array_toList_append, List.mem_append] at h
      exact h.elim (fun h => hx.2.1 h hp) (fun h => hy.2.1 h hp)
    · intro x h hp
      rw [array_toList_append, List.mem_append] at h
      exact h.elim (fun h => hx.2.2.1 h hp) (fun h => hy.2.2.1 h hp)
    · intro x h hp
      rw [array_toList_append, List.mem_append] at h
      exact h.elim (fun h => hx.2.2.2 h hp) (fun h => hy.2.2.2 h hp)

theorem disjoint_array_append {xs ys zs : Array ℕ}
    (hy : xs.toList.Disjoint ys.toList) (hz : xs.toList.Disjoint zs.toList) :
    xs.toList.Disjoint (ys ++ zs).toList := by
  intro x hx h
  rw [array_toList_append, List.mem_append] at h
  exact h.elim (hy hx) (hz hx)

end ElevenSquare.Pending.ExclusionCounts
#print axioms ElevenSquare.Pending.ExclusionCounts.BaselineGood.append
