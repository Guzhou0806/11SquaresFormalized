import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window022.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window022.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window022.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-27609374999943/28691406250000), (410265624999153/3672500000000000), (-15931300776409781133830983734523223944664272719/14028950000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-27609374999943/28691406250000), (410265624999153/3672500000000000), (-15931300776409781133830983734523223944664272719/14028950000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-410265624999153/3672500000000000), (-27609374999943/28691406250000), (-218332205645859588855704374370345954474219361/109601171875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-410265624999153/3672500000000000), (-27609374999943/28691406250000), (-218332205645859588855704374370345954474219361/109601171875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window022
