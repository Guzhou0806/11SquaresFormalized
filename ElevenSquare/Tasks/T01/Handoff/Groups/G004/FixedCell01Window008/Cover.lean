import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-20001084479000410693494371953/47750000000000000000000000000), (18449633035867035385990508739/152800000000000000000000000000), (-15353761035245468411757580102818003886006749209126631351917/33425132324800000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-20001084479000410693494371953/47750000000000000000000000000), (18449633035867035385990508739/152800000000000000000000000000), (-15353761035245468411757580102818003886006749209126631351917/33425132324800000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-20001084479000410693494371953/47750000000000000000000000000), (-18449633035867035385990508739/152800000000000000000000000000), (-205047517597824553671460971566445780811446529425098878018762805370257/319210013701840000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(-20001084479000410693494371953/47750000000000000000000000000), (-18449633035867035385990508739/152800000000000000000000000000), (-205047517597824553671460971566445780811446529425098878018762805370257/319210013701840000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-832/1193), (855/1193), (-51015293994378484710229801787171333/208907077030000000000000000000000000)⟩ :: nodeSource001 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource001, nodeSource007]
  change node007.Check (baselineFlip ⟨(-832/1193), (855/1193), (-51015293994378484710229801787171333/208907077030000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node007_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-855/1193), (-832/1193), (-127477425529965817795621873072359475591/83562830812000000000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-855/1193), (-832/1193), (-127477425529965817795621873072359475591/83562830812000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window008
