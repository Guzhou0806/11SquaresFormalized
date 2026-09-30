import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window030.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window030.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window030.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window030
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-128512/128537), (2535/128537), (-2914105181044370530137610597989605771470701567/2028234620906151820000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-128512/128537), (2535/128537), (-2914105181044370530137610597989605771470701567/2028234620906151820000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-2535/128537), (-128512/128537), (-1083763385114625182736333101309073617418541871/2028234620906151820000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-2535/128537), (-128512/128537), (-1083763385114625182736333101309073617418541871/2028234620906151820000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window030
