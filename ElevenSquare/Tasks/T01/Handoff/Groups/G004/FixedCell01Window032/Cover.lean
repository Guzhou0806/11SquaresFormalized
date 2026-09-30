import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window032.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window032.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window032
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-130560/130561), (511/130561), (-3087863022188442372690643960797873332046074807/2125431380456922860000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-130560/130561), (511/130561), (-3087863022188442372690643960797873332046074807/2125431380456922860000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window032
