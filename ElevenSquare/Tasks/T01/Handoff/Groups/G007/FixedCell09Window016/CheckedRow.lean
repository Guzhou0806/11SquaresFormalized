import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Pair01
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Pair02
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Pair12
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.MedianToPair01
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.MedianToPair02
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.MedianToPair12
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Region000
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Region002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.Region003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016
open ElevenSquare Pending ElevenSquare.Tasks.T01
noncomputable section

def rowCertificate : FixedRow.Certificate where
  targets := [.singleton region000,
    .median medianTarget pair01 pair02 pair12 medianToPair01 medianToPair02 medianToPair12,
    .blocker ((248983/250000), (830121073/500000000)) region002,
    .blocker ((498139531/500000000), (2372449569/1000000000)) region003]
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
    · change pair01.Check [G007.site0, G007.site1] inputRow ∧
          pair02.Check [G007.site0, G007.site2] inputRow ∧
          pair12.Check [G007.site1, G007.site2] inputRow ∧
          BaselinePolygonImplicationCheck medianTarget pair01.polygon medianToPair01 ∧
          BaselinePolygonImplicationCheck medianTarget pair02.polygon medianToPair02 ∧
          BaselinePolygonImplicationCheck medianTarget pair12.polygon medianToPair12
      refine ⟨?_, ?_, ?_, medianToPair01_checked, medianToPair02_checked, medianToPair12_checked⟩
      · have hf : pair01Feature = [G007.site0, G007.site1] := by
          norm_num [pair01Feature, G007.site0, G007.site1, G007.physicalToUnit]
        simpa [← hf] using pair01_checked
      · have hf : pair02Feature = [G007.site0, G007.site2] := by
          norm_num [pair02Feature, G007.site0, G007.site2, G007.physicalToUnit]
        simpa [← hf] using pair02_checked
      · have hf : pair12Feature = [G007.site1, G007.site2] := by
          norm_num [pair12Feature, G007.site1, G007.site2, G007.physicalToUnit]
        simpa [← hf] using pair12_checked
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
  rcases hp with rfl | rfl
  · have hh := hpartners (⟨4, by decide⟩, 6) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨4, by decide⟩)
      hh.1 ⟨4, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell04])
  · have hh := hpartners (⟨8, by decide⟩, 5) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨8, by decide⟩)
      hh.1 ⟨8, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell08])

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window016.capture_from_packing
