import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(-3456/4825), (3367/4825), (1440920233062868022695719/3015625000000000000000000)⟩ :: nodeSource004 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource004, nodeSource006]
  change node006.Check (baselineFlip ⟨(-3456/4825), (3367/4825), (1440920233062868022695719/3015625000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-13078124999973/18847656250000), (1630890624996633/2412500000000000), (6460828858483741993326478584898917347904833241/9215750000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-13078124999973/18847656250000), (1630890624996633/2412500000000000), (6460828858483741993326478584898917347904833241/9215750000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-1630890624996633/2412500000000000), (-13078124999973/18847656250000), (-177106901949875164935491968660436237754646671/71998046875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-1630890624996633/2412500000000000), (-13078124999973/18847656250000), (-177106901949875164935491968660436237754646671/71998046875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window007
