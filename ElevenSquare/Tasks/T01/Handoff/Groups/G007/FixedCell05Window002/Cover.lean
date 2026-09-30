import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node006_checked : node006.Check nodeSource006 targets := by
  refine ⟨node007_checked, ?_⟩
  have he : baselineFlip ⟨(1408/4217), (-3975/4217), (-1743229548896405587706759/2635625000000000000000000)⟩ :: nodeSource006 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource006, nodeSource008]
  change node008.Check (baselineFlip ⟨(1408/4217), (-3975/4217), (-1743229548896405587706759/2635625000000000000000000)⟩ :: nodeSource006) targets
  rw [he]
  exact node008_checked

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-3975/4217), (-1408/4217), (-28061378480012989107931981050020057/16108940000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-3975/4217), (-1408/4217), (-28061378480012989107931981050020057/16108940000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-5328124999989/16472656250000), (77015624999841/84340000000000), (1706094116921997631802960217/2108500000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-5328124999989/16472656250000), (77015624999841/84340000000000), (1706094116921997631802960217/2108500000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(77015624999841/84340000000000), (5328124999989/16472656250000), (4649828086097248370544005217/2108500000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(77015624999841/84340000000000), (5328124999989/16472656250000), (4649828086097248370544005217/2108500000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window002
