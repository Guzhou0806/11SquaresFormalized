import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window010.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window010.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window010.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window010
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(273281249999417/732500000000000), (9843749999979/11445312500000), (138551105967096317023907753389524973945888383/43721093750000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(273281249999417/732500000000000), (9843749999979/11445312500000), (138551105967096317023907753389524973945888383/43721093750000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(9843749999979/11445312500000), (-273281249999417/732500000000000), (3459752243533324730536067579826129171546512391/2798150000000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(9843749999979/11445312500000), (-273281249999417/732500000000000), (3459752243533324730536067579826129171546512391/2798150000000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window010
