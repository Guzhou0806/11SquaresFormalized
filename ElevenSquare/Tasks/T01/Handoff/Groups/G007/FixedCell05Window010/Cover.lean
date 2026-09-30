import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CoverLeaf008
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CoverLeaf011
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010.CoverLeaf012

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node010_checked : node010.Check nodeSource010 targets := by
  refine ⟨node011_checked, ?_⟩
  have he : baselineFlip ⟨(-3937499999991/5265625000000), (3062499999993/6740000000000), (-62441459288254714164483663/168500000000000000000000000)⟩ :: nodeSource010 = nodeSource012 := by
    norm_num [baselineFlip, nodeSource010, nodeSource012]
  change node012.Check (baselineFlip ⟨(-3937499999991/5265625000000), (3062499999993/6740000000000), (-62441459288254714164483663/168500000000000000000000000)⟩ :: nodeSource010) targets
  rw [he]
  exact node012_checked

theorem node006_checked : node006.Check nodeSource006 targets := by
  refine ⟨node007_checked, ?_⟩
  have he : baselineFlip ⟨(3062499999993/6740000000000), (3937499999991/5265625000000), (301927919141224941541961337/168500000000000000000000000)⟩ :: nodeSource006 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource006, nodeSource008]
  change node008.Check (baselineFlip ⟨(3062499999993/6740000000000), (3937499999991/5265625000000), (301927919141224941541961337/168500000000000000000000000)⟩ :: nodeSource006) targets
  rw [he]
  exact node008_checked

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-789379859731327419083819709594139280401831524043752169/3218350000000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-235139993842669310691227678449/955000000000000000000000000000), (123443194477576381887282677473/3820000000000000000000000000000), (-789379859731327419083819709594139280401831524043752169/3218350000000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-1562924602303313733973963433671133185166475177138254019/12873400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-1562924602303313733973963433671133185166475177138254019/12873400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(288/337), (-175/337), (216602820739521710091651/210625000000000000000000)⟩ :: nodeSource001 = nodeSource009 := by
    norm_num [baselineFlip, nodeSource001, nodeSource009]
  change node009.Check (baselineFlip ⟨(288/337), (-175/337), (216602820739521710091651/210625000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node009_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-175/337), (-288/337), (-621365367349040520760809931493369/321835000000000000000000000000000)⟩ :: nodeSource000 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource000, nodeSource010]
  change node010.Check (baselineFlip ⟨(-175/337), (-288/337), (-621365367349040520760809931493369/321835000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node010_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window010
