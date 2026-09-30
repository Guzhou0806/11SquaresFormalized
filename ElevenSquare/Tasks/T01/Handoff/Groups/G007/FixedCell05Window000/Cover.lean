import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node006_checked : node006.Check nodeSource006 targets := by
  refine ⟨node007_checked, ?_⟩
  have he : baselineFlip ⟨(-437499999999/4015625000000), (22312499999949/25700000000000), (129188146431342275308156257/128500000000000000000000000)⟩ :: nodeSource006 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource006, nodeSource008]
  change node008.Check (baselineFlip ⟨(-437499999999/4015625000000), (22312499999949/25700000000000), (129188146431342275308156257/128500000000000000000000000)⟩ :: nodeSource006) targets
  rw [he]
  exact node008_checked

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-255/257), (-32/257), (-1511435020028019663622070856402913/981740000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-255/257), (-32/257), (-1511435020028019663622070856402913/981740000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-437499999999/4015625000000), (22312499999949/25700000000000), (130833224075338515130684257/128500000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-437499999999/4015625000000), (22312499999949/25700000000000), (130833224075338515130684257/128500000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(22312499999949/25700000000000), (437499999999/4015625000000), (237580138000407022184569257/128500000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(22312499999949/25700000000000), (437499999999/4015625000000), (237580138000407022184569257/128500000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000
