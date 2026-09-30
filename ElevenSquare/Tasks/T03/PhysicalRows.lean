import ElevenSquare.Tasks.T03.PhysicalRowInput
import ElevenSquare.Tasks.T03.RefinementRows

namespace ElevenSquare.Pending.T03
noncomputable section

def PhysicalRowInput.resultRow (w : PhysicalRowInput) : PoseRow :=
  ⟨w.band.lo,w.band.hi,w.domain.map IntegerPlane.rational⟩

theorem PhysicalRowInput.contains_result (w : PhysicalRowInput) (r : IntegerRow)
    (vs : List QPoint) (h : w.check r vs = true) (q : UnitSquare)
    (hq : r.row.contains q) (hc : ContainedAtCap q)
    (hold : rationalHull vs ⊆ {p | OpenSquare q p}) : w.resultRow.contains q := by
  obtain ⟨hp,t,ha,hb,haxis⟩ := w.sound r vs h q hq hc hold
  have hcheck := h
  simp only [PhysicalRowInput.check,Bool.and_eq_true] at hcheck
  obtain ⟨_,_,h0,_,h1,_,_⟩ := of_decide_eq_true hcheck.1.1.2
  have h0' : (0:ℝ) ≤ w.band.lo := by exact_mod_cast h0
  have h1' : (w.band.hi:ℝ) ≤ 1 := by exact_mod_cast h1
  refine ⟨?_,t,le_trans h0' ha,le_trans hb h1',ha,hb,haxis⟩
  rwa [integerCarrier_as_polygon] at hp

theorem PhysicalRowInput.impossible (w : PhysicalRowInput) (r : IntegerRow)
    (vs : List QPoint) (h : w.check r vs = true) (he : w.domain=[⟨0,0,-1⟩])
    (q : UnitSquare) (hq : r.row.contains q) (hc : ContainedAtCap q)
    (hold : rationalHull vs ⊆ {p | OpenSquare q p}) : False := by
  have hp := (w.sound r vs h q hq hc hold).1
  rw [he] at hp
  have hh := hp ⟨0,0,-1⟩ (by simp)
  norm_num [IntegerPlane.holds] at hh

def PhysicalRowInput.emptyCertificate (w : PhysicalRowInput) (r : IntegerRow)
    (prior : Owner → List QPoint) (rows : Owner → List PoseRow) (i : Owner)
    (chosen : List QPoint) (h : w.check r (prior i) = true)
    (he : w.domain=[⟨0,0,-1⟩]) : ForwardRows prior rows i chosen where
  before := [r.row]
  after := []
  cover := by
    intro q hq hc hold
    exact False.elim (w.impossible r (prior i) h he q
      ((rowsContain_singleton _ q).mp hq) hc hold)
  owned := by
    intro q hq
    obtain ⟨r,hr,_⟩ := hq
    exact False.elim (List.not_mem_nil r hr)

/-- A physical partner cover preserves its old ownership hypothesis. -/
structure PhysicalRows (vs : List QPoint) where
  before : List PoseRow
  after : List PoseRow
  cover : ∀ q, RowsContain before q → ContainedAtCap q →
    (rationalHull vs ⊆ {p | OpenSquare q p}) → RowsContain after q

def PhysicalRows.append {vs : List QPoint} (a b : PhysicalRows vs) : PhysicalRows vs where
  before := a.before++b.before
  after := a.after++b.after
  cover := by
    intro q hq hc hold
    rw [rowsContain_append] at hq ⊢
    exact hq.elim (fun h => Or.inl (a.cover q h hc hold))
      (fun h => Or.inr (b.cover q h hc hold))

def PhysicalRowInput.partnerCover (w : PhysicalRowInput) (r : IntegerRow)
    (vs : List QPoint) (h : w.check r vs = true) : PhysicalRows vs where
  before := [r.row]
  after := [w.resultRow]
  cover := by
    intro q hq hc hold
    exact (rowsContain_singleton _ q).mpr
      (w.contains_result r vs h q ((rowsContain_singleton _ q).mp hq) hc hold)

theorem PhysicalRows.refined_cover {vs : List QPoint} (w : PhysicalRows vs)
    (entries : List (IntegerRow × RowRefinement))
    (hcheck : RefinementRows.check entries = true)
    (hbefore : RefinementRows.after entries=w.before) (q : UnitSquare)
    (hq : RowsContain (RefinementRows.before entries) q) (hc : ContainedAtCap q)
    (hold : rationalHull vs ⊆ {p | OpenSquare q p}) : RowsContain w.after q := by
  apply w.cover q _ hc hold
  rw [← hbefore]
  exact (RefinementRows.equiv entries hcheck q).mp hq

end
end ElevenSquare.Pending.T03
