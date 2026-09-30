import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.Region000
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.Region001
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.Region002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023
open ElevenSquare Pending ElevenSquare.Tasks.T01
noncomputable section

def rowCertificate : FixedRow.Certificate where
  targets := [.singleton region000,
    .blocker ((313569079679342521477316341/200000000000000000000000000), (140033439907660930894815023/100000000000000000000000000)) region001,
    .blocker ((498139531/500000000), (2372449569/1000000000)) region002]
  cover := node000

theorem row_certificate_checked : rowCertificate.Check inputRow := by
  constructor
  · simpa [rowCertificate, FixedRow.Certificate.polygons, inputRow] using cover_checked
  · intro target htarget
    simp only [rowCertificate, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at htarget
    rcases htarget with rfl | rfl | rfl
    · have hf : region000Feature = [G007.point] := by
        norm_num [region000Feature, G007.point, G007.physicalToUnit]
      simpa [FixedRow.Target.Check, ← hf] using region000_checked
    · simpa [FixedRow.Target.Check, region001Feature] using region001_checked
    · simpa [FixedRow.Target.Check, region002Feature] using region002_checked

theorem blocker_points : rowCertificate.blockerPoints = forbiddenPoints := by
  rfl

theorem row_choice (q : UnitSquare) (hq : inputRow.contains q)
    (hblocked : ∀ p ∈ forbiddenPoints, ¬ OpenSquare q (realPoint p)) :
    OpenSquare q (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 q := by
  apply FixedRow.row_choice rowCertificate inputRow row_certificate_checked q hq
  simpa [blocker_points] using hblocked

theorem capture_from_packing (P : Packing 11 coverCap) (hc : IsCharted P)
    (i : Owner) (partner : Fin 16 → Owner)
    (hrow : inputRow.contains (P.squares i))
    (hpartners : ∀ item ∈ blockerIndices,
      i ≠ partner item.1 ∧
        ClosedCell item.1
          (normalizeCenter (P.squares (partner item.1)).center)) :
    OpenSquare (P.squares i) (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 (P.squares i) := by
  apply FixedRow.packing_row_choice rowCertificate inputRow row_certificate_checked
    P i hrow
  rw [blocker_points]
  intro p hp
  simp only [forbiddenPoints, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · have hh := hpartners (⟨5, by decide⟩, 0) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨5, by decide⟩)
      hh.1 ⟨5, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell05])
  · have hh := hpartners (⟨8, by decide⟩, 5) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨8, by decide⟩)
      hh.1 ⟨8, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell08])

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window023.capture_from_packing
