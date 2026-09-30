import ElevenSquare.Tasks.T03.IntegerRowTrace

namespace ElevenSquare.Pending.T03
noncomputable section

def IntegerRow.withInterval (r : IntegerRow) (lo hi : ℚ) : IntegerRow :=
  ⟨lo,hi,r.planes⟩

/-- Closed interval splitting. Both children retain their common endpoint. -/
inductive RowRefinement where
  | leaf
  | split (mid : ℚ) (left right : RowRefinement)

def RowRefinement.rows : RowRefinement → IntegerRow → List IntegerRow
  | .leaf, r => [r]
  | .split mid a b, r => a.rows (r.withInterval r.lo mid) ++ b.rows (r.withInterval mid r.hi)

def RowRefinement.check : RowRefinement → IntegerRow → Bool
  | .leaf, _ => true
  | .split mid a b, r => decide (r.lo ≤ mid ∧ mid ≤ r.hi) &&
      a.check (r.withInterval r.lo mid) && b.check (r.withInterval mid r.hi)

theorem RowRefinement.equiv (tree : RowRefinement) (r : IntegerRow)
    (h : tree.check r = true) (q : UnitSquare) :
    RowsContain ((tree.rows r).map IntegerRow.row) q ↔ r.row.contains q := by
  induction tree generalizing r with
  | leaf => simpa [rows] using rowsContain_singleton r.row q
  | split mid a b iha ihb =>
    simp only [check,Bool.and_eq_true] at h
    have ha := iha (r.withInterval r.lo mid) h.1.2
    have hb := ihb (r.withInterval mid r.hi) h.2
    have hlo : (r.lo:ℝ) ≤ (mid:ℝ) := by exact_mod_cast (of_decide_eq_true h.1.1).1
    have hhi : (mid:ℝ) ≤ (r.hi:ℝ) := by exact_mod_cast (of_decide_eq_true h.1.1).2
    simp only [rows,List.map_append,rowsContain_append,ha,hb]
    constructor
    · rintro (⟨hc,t,ht0,ht1,hta,htb,haxis⟩ | ⟨hc,t,ht0,ht1,hta,htb,haxis⟩)
      · exact ⟨hc,t,ht0,ht1,hta,le_trans htb hhi,haxis⟩
      · exact ⟨hc,t,ht0,ht1,le_trans hlo hta,htb,haxis⟩
    · rintro ⟨hc,t,ht0,ht1,hta,htb,haxis⟩
      rcases le_total t (mid:ℝ) with ht | ht
      · exact Or.inl ⟨hc,t,ht0,ht1,hta,ht,haxis⟩
      · exact Or.inr ⟨hc,t,ht0,ht1,ht,htb,haxis⟩

end
end ElevenSquare.Pending.T03
