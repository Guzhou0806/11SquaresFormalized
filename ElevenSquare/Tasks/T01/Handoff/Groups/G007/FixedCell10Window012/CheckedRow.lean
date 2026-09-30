import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.Region000
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.Region001
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.Region002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.Region003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012
open ElevenSquare Pending ElevenSquare.Tasks.T01
noncomputable section

def rowCertificate : FixedRow.Certificate where
  targets := [.singleton region000,
    .blocker ((288115159/100000000), (447239513/200000000)) region001,
    .blocker ((115167512002955994035477669/50000000000000000000000000), (324616765542600606379986307/100000000000000000000000000)) region002,
    .blocker ((2333200481/1000000000), (799588769/250000000)) region003]
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
  rcases hp with rfl | rfl | rfl
  · have hh := hpartners (⟨11, by decide⟩, 9) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨11, by decide⟩)
      hh.1 ⟨11, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell11])
  · have hh := hpartners (⟨14, by decide⟩, 0) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨14, by decide⟩)
      hh.1 ⟨14, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell14])
  · have hh := hpartners (⟨14, by decide⟩, 5) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨14, by decide⟩)
      hh.1 ⟨14, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell14])

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.capture_from_packing
