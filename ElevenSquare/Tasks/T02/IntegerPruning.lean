import ElevenSquare.Tasks.T02.IntegerCoverBridge
import ElevenSquare.Tasks.T02.FinitePruning

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- The same pruning conclusion, using the integer coverage proof independently
of the older rational cover stored in the row record. Strict-core and forbidden
geometry checks remain unchanged. -/
theorem integer_row_pruning_sound (s : PoseState) (i : Owner) (r : PoseRow)
    (c : RowPruningCertificate) (cover : IntegerCover.RationalCertificate)
    (hc : cover.Check r.centers c.targets)
    (hf : ∀ piece ∈ c.forbidden, piece.Check s i r)
    (q : UnitSquare) (hq : r.contains q) :
    RowsContain (c.keptRows r) q ∨
      ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
        CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q := by
  obtain ⟨poly, hpoly, hp⟩ := IntegerCover.rational_certificate_sound
    r.centers c.targets cover hc q.center hq.1
  rcases List.mem_append.mp hpoly with hkeep | hforbid
  · left
    exact ⟨{r with centers := poly}, List.mem_map.mpr ⟨poly, hkeep, rfl⟩, hp, hq.2⟩
  · right
    obtain ⟨piece, hm, rfl⟩ := List.mem_map.mp hforbid
    have h := hf piece hm
    refine ⟨piece.partner, h.1, rationalHull piece.core, ?_, ?_⟩
    · exact baseline_row_core_checked r piece.core h.2.2.2 q hq
    · exact checked_forbidden_polygon (s.owned piece.partner) piece.core
        piece.vertices piece.polygon piece.witnesses h.2.1 h.2.2.1 hp

end
end ElevenSquare.Tasks.T02
