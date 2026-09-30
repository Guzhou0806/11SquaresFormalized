import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window003.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window003.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-4071/4121), (-640/4121), (-13745014565082216564526360090066362237477/8591418889430000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-4071/4121), (-640/4121), (-13745014565082216564526360090066362237477/8591418889430000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window003
