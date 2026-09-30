import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window001.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window001.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-16375/16393), (-768/16393), (-6435557952346435429850837593533331150657047/4270950844820140000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-16375/16393), (-768/16393), (-6435557952346435429850837593533331150657047/4270950844820140000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window001
