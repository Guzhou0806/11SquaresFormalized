import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.Region000
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.Region001
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.Region002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.Region003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000
open ElevenSquare Pending ElevenSquare.Tasks.T01
noncomputable section

def rowCertificate : FixedRow.Certificate where
  targets :=
    [.singleton region000,
     .blocker ((288115159/100000000), (447239513/200000000)) region001,
     .blocker ((115167512002955994035477669/50000000000000000000000000),
       (324616765542600606379986307/100000000000000000000000000)) region002,
     .blocker ((2305035533/1000000000), (1474001781/500000000)) region003]
  cover := node000

theorem row_certificate_checked : rowCertificate.Check inputRow := by
  constructor
  · simpa [rowCertificate, FixedRow.Certificate.polygons, inputRow] using cover_checked
  · intro target htarget
    simp only [rowCertificate, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at htarget
    rcases htarget with rfl | rfl | rfl | rfl
    · have hf : region000Feature = [G007.point] := by
        norm_num [region000Feature, G007.point, G007.physicalToUnit]
      simpa [FixedRow.Target.Check, ← hf] using region000_checked
    · simpa [FixedRow.Target.Check, region001Feature] using region001_checked
    · simpa [FixedRow.Target.Check, region002Feature] using region002_checked
    · simpa [FixedRow.Target.Check, region003Feature] using region003_checked

theorem blocker_points : rowCertificate.blockerPoints = forbiddenPoints := by
  rfl

theorem row_choice (q : UnitSquare) (hq : inputRow.contains q)
    (hblocked : ∀ p ∈ forbiddenPoints, ¬ OpenSquare q (realPoint p)) :
    OpenSquare q (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 q := by
  apply FixedRow.row_choice rowCertificate inputRow row_certificate_checked q hq
  simpa [blocker_points] using hblocked

def rosterIndices : List (Fin 16 × ℕ) :=
  [(⟨11, by decide⟩, 2), (⟨14, by decide⟩, 0), (⟨14, by decide⟩, 4)]

theorem roster_points :
    FixedOwnership.pointsOfRosterIndices rosterIndices = forbiddenPoints := by
  rfl

theorem capture_from_packing (P : Packing 11 coverCap) (hc : IsCharted P)
    (i : Owner) (partner : Fin 16 → Owner)
    (hrow : inputRow.contains (P.squares i))
    (hpartners : ∀ item ∈ blockerIndices,
      i ≠ partner item.1 ∧
        ClosedCell item.1
          (normalizeCenter (P.squares (partner item.1)).center)) :
    OpenSquare (P.squares i) (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 (P.squares i) := by
  have h11 := hpartners (⟨11, by decide⟩, 9) (by simp [blockerIndices])
  have h140 := hpartners (⟨14, by decide⟩, 0) (by simp [blockerIndices])
  have h149 := hpartners (⟨14, by decide⟩, 9) (by simp [blockerIndices])
  have hne : ∀ item ∈ rosterIndices, i ≠ partner item.1 := by
    intro item hi
    simp only [rosterIndices, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact h11.1
    · exact h140.1
    · exact h149.1
  have hcell : ∀ item ∈ rosterIndices,
      ClosedCell item.1
        (normalizeCenter (P.squares (partner item.1)).center) := by
    intro item hi
    simp only [rosterIndices, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact h11.2
    · exact h140.2
    · exact h149.2
  have hindex : ∀ item ∈ rosterIndices,
      item.2 < (G007.Candidate.ownedRoster item.1).length := by
    intro item hi
    simp only [rosterIndices, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals decide
  apply FixedRow.packing_row_choice rowCertificate inputRow row_certificate_checked
    P i hrow
  rw [blocker_points, ← roster_points]
  exact FixedOwnership.roster_index_points_owned P hc i partner rosterIndices
    hne hcell hindex

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window000.capture_from_packing
