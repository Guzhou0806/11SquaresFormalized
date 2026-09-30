import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node006_checked : node006.Check nodeSource006 targets := by
  refine ⟨node007_checked, ?_⟩
  have he : baselineFlip ⟨(-6093749999987/9320312500000), (80156249999829/119300000000000), (21392901803770143059485193/596500000000000000000000000)⟩ :: nodeSource006 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource006, nodeSource008]
  change node008.Check (baselineFlip ⟨(-6093749999987/9320312500000), (80156249999829/119300000000000), (21392901803770143059485193/596500000000000000000000000)⟩ :: nodeSource006) targets
  rw [he]
  exact node008_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-5453338851968991337416344541537738525296880745180822091/45572600000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-5453338851968991337416344541537738525296880745180822091/45572600000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(832/1193), (-855/1193), (302599007309978323454549/745625000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(832/1193), (-855/1193), (302599007309978323454549/745625000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-855/1193), (-832/1193), (-8841982651097349565055689878882313/4557260000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(-855/1193), (-832/1193), (-8841982651097349565055689878882313/4557260000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window008
