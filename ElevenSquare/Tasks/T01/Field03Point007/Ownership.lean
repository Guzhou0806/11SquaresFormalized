import ElevenSquare.Tasks.T01.Field03Point007.Leaf000
import ElevenSquare.Tasks.T01.Field03Point007.Leaf001
import ElevenSquare.Tasks.T01.Field03Point007.Leaf002
import ElevenSquare.Tasks.T01.Field03Point007.Leaf003
import ElevenSquare.Tasks.T01.Field03Point007.Leaf004
import ElevenSquare.Tasks.T01.Field03Point007.Leaf005
import ElevenSquare.Tasks.T01.Field03Point007.Leaf006
import ElevenSquare.Tasks.T01.Field03Point007.Leaf007
import ElevenSquare.Tasks.T01.Field03Point007.Leaf008
import ElevenSquare.Tasks.T01.Field03Point007.Leaf009
import ElevenSquare.Tasks.T01.Field03Point007.Leaf010
import ElevenSquare.Tasks.T01.Field03Point007.Leaf011
import ElevenSquare.Tasks.T01.Field03Point007.Leaf012
import ElevenSquare.Tasks.T01.Field03Point007.Leaf013
import ElevenSquare.Tasks.T01.Field03Point007.Leaf014
import ElevenSquare.Tasks.T01.Field03Point007.Leaf015
import ElevenSquare.Tasks.T01.Field03Point007.Leaf016
import ElevenSquare.Tasks.T01.Field03Point007.Leaf017
import ElevenSquare.Tasks.T01.Field03Point007.Leaf018

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def certificate : WallOwnershipCertificate :=
  .split (67/128) (.split (73/256) (.split (85/512) (.split (109/1024) (.split (157/2048) (.split (253/4096) (.leaf leaf000) (.leaf leaf001)) (.leaf leaf002)) (.leaf leaf003)) (.split (231/1024) (.leaf leaf004) (.leaf leaf005))) (.split (207/512) (.leaf leaf006) (.leaf leaf007))) (.split (195/256) (.split (329/512) (.split (597/1024) (.split (1133/2048) (.leaf leaf008) (.leaf leaf009)) (.split (1255/2048) (.leaf leaf010) (.leaf leaf011))) (.leaf leaf012)) (.split (451/512) (.leaf leaf013) (.split (963/1024) (.leaf leaf014) (.split (1987/2048) (.leaf leaf015) (.split (4035/4096) (.leaf leaf016) (.split (8131/8192) (.leaf leaf017) (.leaf leaf018)))))))

theorem certificate_checked : certificate.Check 0 [point] (3/64) 1 := by
  unfold certificate
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
          · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
            · exact leaf000_checked
            · exact leaf001_checked
          · exact leaf002_checked
        · exact leaf003_checked
      · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · exact leaf004_checked
        · exact leaf005_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact leaf006_checked
      · exact leaf007_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
          · exact leaf008_checked
          · exact leaf009_checked
        · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
          · exact leaf010_checked
          · exact leaf011_checked
      · exact leaf012_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact leaf013_checked
      · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · exact leaf014_checked
        · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
          · exact leaf015_checked
          · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
            · exact leaf016_checked
            · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
              · exact leaf017_checked
              · exact leaf018_checked

/-- Actual archived seed point: ownership for contained squares in closed cell 0,
with the closed chart interval from 3/64 to 1 covered. -/
theorem point_owned (q : UnitSquare)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, (3/64 : ℝ) ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint point) := by
  obtain ⟨t, htlo, hthi, ha⟩ := hchart
  have hh := wall_ownership_sound 0 [point] certificate (3/64) 1 certificate_checked q hcell hcont t (by linarith) (by simpa using hthi) ha (by simpa using htlo) (by simpa using hthi)
  exact hh point (by simp)

end
end ElevenSquare.Tasks.T01.Field03Point007
