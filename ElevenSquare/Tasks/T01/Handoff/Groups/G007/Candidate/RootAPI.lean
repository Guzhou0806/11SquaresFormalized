import ElevenSquare.Tasks.T01.Handoff.Plan
import ElevenSquare.Tasks.T01.ChartSubdivision
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def rowsAt (rows5 rows9 rows10 : List PoseRow) (cell : Fin 16) : List PoseRow :=
  if cell.val = 5 then rows5 else
  if cell.val = 9 then rows9 else
  if cell.val = 10 then rows10 else
  uniformRows 32 (baselineCellPolygon cell)

def rootStateOfRows (m : Finset (Fin 16))
    (rows5 rows9 rows10 : List PoseRow) : PoseState where
  rows := fun i => rowsAt rows5 rows9 rows10 (baselineRoles m i)
  owned := fun i => ownedRoster (baselineRoles m i)

theorem root_valid_of_cell_covers (m : Finset (Fin 16))
    (rows5 rows9 rows10 : List PoseRow)
    (h5 : ∀ q : UnitSquare,
      ClosedCell 5 (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      RowsContain rows5 q)
    (h9 : ∀ q : UnitSquare,
      ClosedCell 9 (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      RowsContain rows9 q)
    (h10 : ∀ q : UnitSquare,
      ClosedCell 10 (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      RowsContain rows10 q)
    (hfull : OwnedRosterFullChart) :
    RootValid m (rootStateOfRows m rows5 rows9 rows10) := by
  intro P hc hocc
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  refine ⟨perm, ?_, ?_⟩
  · intro i
    let c := baselineRoles m i
    have hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        ((relabelPacking P perm).squares i).axis = chartAxis t := hc (perm i)
    change RowsContain (rowsAt rows5 rows9 rows10 c)
      ((relabelPacking P perm).squares i)
    by_cases hc5 : c.val = 5
    · have he : c = (⟨5, by decide⟩ : Fin 16) := Fin.ext hc5
      have hc' : ClosedCell c (normalizeCenter ((relabelPacking P perm).squares i).center) := hcell i
      rw [he] at hc'
      simp only [rowsAt, hc5, ite_true]
      exact h5 _ hc' ((relabelPacking P perm).contained i) hchart
    · by_cases hc9 : c.val = 9
      · have he : c = (⟨9, by decide⟩ : Fin 16) := Fin.ext hc9
        have hc' : ClosedCell c (normalizeCenter ((relabelPacking P perm).squares i).center) := hcell i
        rw [he] at hc'
        simp only [rowsAt, hc5, hc9, ite_true, ite_false]
        exact h9 _ hc' ((relabelPacking P perm).contained i) hchart
      · by_cases hc10 : c.val = 10
        · have he : c = (⟨10, by decide⟩ : Fin 16) := Fin.ext hc10
          have hc' : ClosedCell c (normalizeCenter ((relabelPacking P perm).squares i).center) := hcell i
          rw [he] at hc'
          simp only [rowsAt, hc5, hc9, hc10, ite_true, ite_false]
          exact h10 _ hc' ((relabelPacking P perm).contained i) hchart
        · simp only [rowsAt, hc5, hc9, hc10, ite_false]
          apply (uniformRows_contains 32 (by decide) _ _).mpr
          exact ⟨baselineCellPolygon_contains (hcell i), hchart⟩
  · intro i
    apply hull_owned_of_vertices
    intro v hv
    exact hfull (baselineRoles m i) _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i)) v hv

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.root_valid_of_cell_covers
