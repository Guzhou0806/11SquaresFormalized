import ElevenSquare.Tasks.T01.Field03Point007Early.Leaf000
import ElevenSquare.Tasks.T01.Field03Point007Early.Leaf001
import ElevenSquare.Tasks.T01.Field03Point007Early.Leaf002
import ElevenSquare.Tasks.T01.Field03Point007Early.Leaf003
import ElevenSquare.Tasks.T01.Field03Point007Early.Leaf004
import ElevenSquare.Tasks.T01.Field03Point007Early.Leaf005
import ElevenSquare.Tasks.T01.Field03Point007Early.Leaf006

namespace ElevenSquare.Tasks.T01.Field03Point007Early
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def certificate : WallOwnershipCertificate :=
  .split (3/128) (.split (3/256) (.split (3/512) (.split (3/1024) (.leaf leaf000) (.leaf leaf001)) (.leaf leaf002)) (.split (9/512) (.leaf leaf003) (.leaf leaf004))) (.split (9/256) (.leaf leaf005) (.leaf leaf006))

theorem certificate_checked : certificate.Check 0 [point] 0 (3/64) := by
  unfold certificate
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · exact leaf000_checked
        · exact leaf001_checked
      · exact leaf002_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact leaf003_checked
      · exact leaf004_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · exact leaf005_checked
    · exact leaf006_checked

/-- Actual archived seed point: ownership for contained squares in closed cell 0,
with the closed chart interval from 0 to 3/64 covered. -/
theorem point_owned (q : UnitSquare)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ (3/64 : ℝ) ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint point) := by
  obtain ⟨t, htlo, hthi, ha⟩ := hchart
  have hh := wall_ownership_sound 0 [point] certificate 0 (3/64) certificate_checked q hcell hcont t (by simpa using htlo) (by linarith) ha (by simpa using htlo) (by simpa using hthi)
  exact hh point (by simp)

end
end ElevenSquare.Tasks.T01.Field03Point007Early
