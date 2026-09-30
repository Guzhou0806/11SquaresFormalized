import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-125440/125561), (5511/125561), (-349738841271352245527360285932706689/247483809002354000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-125440/125561), (5511/125561), (-349738841271352245527360285932706689/247483809002354000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-5511/125561), (-125440/125561), (-274571630488745253159093413933283354319993199/472694075194496140000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-5511/125561), (-125440/125561), (-274571630488745253159093413933283354319993199/472694075194496140000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window027
