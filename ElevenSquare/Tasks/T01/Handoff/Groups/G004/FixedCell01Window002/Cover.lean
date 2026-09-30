import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window002.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window002.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-4087/4105), (-384/4105), (-105687321934392931574149875354399991376983/68006437405100000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-4087/4105), (-384/4105), (-105687321934392931574149875354399991376983/68006437405100000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window002
