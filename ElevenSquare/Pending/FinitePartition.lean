import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
namespace ElevenSquare.Pending

theorem finite_partition_of_cards (B P R C : Finset ℕ)
    (hb : B.card = 1931) (hp : P.card = 76) (hr : R.card = 173) (hc : C.card = 4)
    (hbp : Disjoint B P) (hbr : Disjoint B R) (hbc : Disjoint B C)
    (hpr : Disjoint P R) (hpc : Disjoint P C) (hrc : Disjoint R C)
    (hB : B ⊆ Finset.range 2184) (hP : P ⊆ Finset.range 2184)
    (hR : R ⊆ Finset.range 2184) (hC : C ⊆ Finset.range 2184) :
    B ∪ P ∪ R = Finset.range 2184 \ C := by
  have hd : Disjoint (B ∪ P) R := Finset.disjoint_union_left.mpr ⟨hbr, hpr⟩
  have he : Disjoint (B ∪ P ∪ R) C :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hbc, hpc⟩, hrc⟩
  have hn : (B ∪ P ∪ R ∪ C).card = 2184 := by
    rw [Finset.card_union_of_disjoint he, Finset.card_union_of_disjoint hd,
      Finset.card_union_of_disjoint hbp, hb, hp, hr, hc]
  have hs : B ∪ P ∪ R ∪ C ⊆ Finset.range 2184 :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset hB hP) hR) hC
  have hall : B ∪ P ∪ R ∪ C = Finset.range 2184 :=
    Finset.eq_of_subset_of_card_le hs (by rw [Finset.card_range, hn])
  ext x
  constructor
  · intro hx
    exact Finset.mem_sdiff.mpr ⟨hs (Finset.mem_union_left C hx),
      fun hc => (Finset.disjoint_left.mp he) hx hc⟩
  · intro hx
    obtain ⟨hx, hnc⟩ := Finset.mem_sdiff.mp hx
    rw [← hall, Finset.mem_union] at hx
    exact hx.resolve_right hnc

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.finite_partition_of_cards
