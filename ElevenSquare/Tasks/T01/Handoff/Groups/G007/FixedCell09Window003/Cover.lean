import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-474541852731033778078372220698714571474680943898128277/2110550000000000000000000000000000000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-474541852731033778078372220698714571474680943898128277/2110550000000000000000000000000000000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(-576/1105), (943/1105), (764554872934903346960147/690625000000000000000000)⟩ :: nodeSource004 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource004, nodeSource008]
  change node008.Check (baselineFlip ⟨(-576/1105), (943/1105), (764554872934903346960147/690625000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node008_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-4218749999991/8632812500000), (442031249999057/552500000000000), (2866998434870676633023032101183670390163359889/2110550000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-4218749999991/8632812500000), (442031249999057/552500000000000), (2866998434870676633023032101183670390163359889/2110550000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-442031249999057/552500000000000), (-4218749999991/8632812500000), (-74247097568668631308765325391533764483059307/32977343750000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-442031249999057/552500000000000), (-4218749999991/8632812500000), (-74247097568668631308765325391533764483059307/32977343750000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window003
