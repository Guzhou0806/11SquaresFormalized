import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.CoverLeaf008
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node007_checked : node007.Check nodeSource007 targets := by
  refine ⟨node008_checked, ?_⟩
  have he : baselineFlip ⟨(-5504/5945), (2247/5945), (-1855170840943222549950137/3715625000000000000000000)⟩ :: nodeSource007 = nodeSource009 := by
    norm_num [baselineFlip, nodeSource007, nodeSource009]
  change node009.Check (baselineFlip ⟨(-5504/5945), (2247/5945), (-1855170840943222549950137/3715625000000000000000000)⟩ :: nodeSource007) targets
  rw [he]
  exact node009_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(1088390624997753/2972500000000000), (20828124999957/23222656250000), (1380995880834397989854884389/594500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(1088390624997753/2972500000000000), (20828124999957/23222656250000), (1380995880834397989854884389/594500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(20828124999957/23222656250000), (-1088390624997753/2972500000000000), (448594703214366697124813589/594500000000000000000000000)⟩ :: nodeSource004 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource004, nodeSource010]
  change node010.Check (baselineFlip ⟨(20828124999957/23222656250000), (-1088390624997753/2972500000000000), (448594703214366697124813589/594500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node010_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-20828124999957/23222656250000), (1088390624997753/2972500000000000), (-4715560060303300602248290683439628785325880519/11354950000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-20828124999957/23222656250000), (1088390624997753/2972500000000000), (-4715560060303300602248290683439628785325880519/11354950000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-1088390624997753/2972500000000000), (-20828124999957/23222656250000), (-206939248744185791426727777837458761330085439/88710546875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-1088390624997753/2972500000000000), (-20828124999957/23222656250000), (-206939248744185791426727777837458761330085439/88710546875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window018
