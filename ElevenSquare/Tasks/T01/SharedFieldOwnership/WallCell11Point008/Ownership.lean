import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf000
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf001
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf002
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf003
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf004
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf005
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf006
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf007
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf008
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf009
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf010
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf011
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf012
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf013
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf014
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf015
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf016
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf017
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf018
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Leaf019

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def certificate : WallOwnershipCertificate :=
  .split (1/2) (.split (1/4) (.split (1/8) (.split (1/16) (.leaf leaf000) (.split (3/32) (.leaf leaf001) (.leaf leaf002))) (.split (3/16) (.split (5/32) (.split (9/64) (.leaf leaf003) (.leaf leaf004)) (.split (11/64) (.split (21/128) (.leaf leaf005) (.leaf leaf006)) (.split (23/128) (.leaf leaf007) (.leaf leaf008)))) (.split (7/32) (.split (13/64) (.split (25/128) (.leaf leaf009) (.leaf leaf010)) (.split (27/128) (.leaf leaf011) (.leaf leaf012))) (.split (15/64) (.leaf leaf013) (.leaf leaf014))))) (.leaf leaf015)) (.split (3/4) (.split (5/8) (.leaf leaf016) (.leaf leaf017)) (.split (7/8) (.leaf leaf018) (.leaf leaf019)))

theorem certificate_checked : certificate.Check 11 [point] 0 1 := by
  unfold certificate
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · exact leaf000_checked
        · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
          · exact leaf001_checked
          · exact leaf002_checked
      · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
        · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
          · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
            · exact leaf003_checked
            · exact leaf004_checked
          · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
            · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
              · exact leaf005_checked
              · exact leaf006_checked
            · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
              · exact leaf007_checked
              · exact leaf008_checked
        · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
          · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
            · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
              · exact leaf009_checked
              · exact leaf010_checked
            · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
              · exact leaf011_checked
              · exact leaf012_checked
          · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
            · exact leaf013_checked
            · exact leaf014_checked
    · exact leaf015_checked
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact leaf016_checked
      · exact leaf017_checked
    · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · exact leaf018_checked
      · exact leaf019_checked

/-- Strict ownership for the entire closed orientation chart in cell 11. -/
theorem point_owned (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint point) := by
  have hh := checked_wall_owned_hull 11 [point] certificate
    certificate_checked q hcell hcont hchart
  exact hh (subset_convexHull ℝ _ ⟨point, by simp, rfl⟩)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
