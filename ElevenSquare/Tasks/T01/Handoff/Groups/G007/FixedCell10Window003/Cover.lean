import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(4218749999991/8632812500000), (-442031249999057/552500000000000), (-87590450808479234121608179/110500000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(4218749999991/8632812500000), (-442031249999057/552500000000000), (-87590450808479234121608179/110500000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(442031249999057/552500000000000), (4218749999991/8632812500000), (103231091098818403769702957300908764483059307/32977343750000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(442031249999057/552500000000000), (4218749999991/8632812500000), (103231091098818403769702957300908764483059307/32977343750000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(4218749999991/8632812500000), (-442031249999057/552500000000000), (-1012022848941091195523023658983670390163359889/2110550000000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(4218749999991/8632812500000), (-442031249999057/552500000000000), (-1012022848941091195523023658983670390163359889/2110550000000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window003
