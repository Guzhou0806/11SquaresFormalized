import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window027.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window027.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window027
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-58975/72097), (-41472/72097), (-383078657123491740003841354249800862230111/224765593242783200000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-58975/72097), (-41472/72097), (-383078657123491740003841354249800862230111/224765593242783200000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window027
