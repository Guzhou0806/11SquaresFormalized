import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Pair01
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Pair02
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Pair12
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.MedianToPair01
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.MedianToPair02
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.MedianToPair12
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Region001
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Region002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Region003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.Region004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedRow
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013
open ElevenSquare Pending ElevenSquare.Tasks.T01
noncomputable section

def rowCertificate : FixedRow.Certificate where
  targets := [.median medianTarget pair01 pair02 pair12 medianToPair01 medianToPair02 medianToPair12,
    .blocker ((1572048057/1000000000), (232270007/250000000)) region001,
    .blocker ((464596403987128110649685633/200000000000000000000000000), (22480315265430140099670659/25000000000000000000000000)) region002,
    .blocker ((159319997167449384989195311/200000000000000000000000000), (165192385068974431749720049/100000000000000000000000000)) region003,
    .blocker ((248983/250000), (65635441/40000000)) region004]
  cover := node000

theorem row_certificate_checked : rowCertificate.Check inputRow := by
  constructor
  · simpa [rowCertificate, FixedRow.Certificate.polygons, inputRow] using cover_checked
  · intro target htarget
    simp only [rowCertificate, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at htarget
    rcases htarget with rfl | rfl | rfl | rfl | rfl
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
    · simpa [FixedRow.Target.Check, region001Feature] using region001_checked
    · simpa [FixedRow.Target.Check, region002Feature] using region002_checked
    · simpa [FixedRow.Target.Check, region003Feature] using region003_checked
    · simpa [FixedRow.Target.Check, region004Feature] using region004_checked

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
  rcases hp with rfl | rfl | rfl | rfl
  · have hh := hpartners (⟨1, by decide⟩, 6) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨1, by decide⟩)
      hh.1 ⟨1, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell01])
  · have hh := hpartners (⟨2, by decide⟩, 0) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨2, by decide⟩)
      hh.1 ⟨2, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell02])
  · have hh := hpartners (⟨4, by decide⟩, 0) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨4, by decide⟩)
      hh.1 ⟨4, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell04])
  · have hh := hpartners (⟨4, by decide⟩, 5) (by simp [blockerIndices])
    exact FixedOwnership.blocker_owned_for_partner P hc i (partner ⟨4, by decide⟩)
      hh.1 ⟨4, by decide⟩ hh.2 _ (by simp [G007.Candidate.ownedRoster,
        G007.Candidate.ownedRosterCell04])

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.capture_from_packing
