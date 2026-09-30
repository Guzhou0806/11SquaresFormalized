import ElevenSquare.Cover

namespace ElevenSquare.Tasks.T02
noncomputable section

/-- The actual site cells cannot be transported by the naive quarter-turn of
4-by-4 grid indices. This exact counterexample prevents an invalid shortcut. -/
theorem closed_cells_not_naive_quarter_turn :
    ∃ p : Point, ClosedCell (0 : Fin 16) p ∧
      ¬ ClosedCell (3 : Fin 16) (1 - p.2, p.1) := by
  refine ⟨((3/50 : ℝ), (13/50 : ℝ)), ?_, ?_⟩
  · constructor
    · norm_num [InUnitBox]
    · intro j
      fin_cases j <;> norm_num [coordinateDistanceSq, coverSite]
  · intro h
    have hj := h.2 (2 : Fin 16)
    norm_num [coordinateDistanceSq, coverSite] at hj

end
end ElevenSquare.Tasks.T02
