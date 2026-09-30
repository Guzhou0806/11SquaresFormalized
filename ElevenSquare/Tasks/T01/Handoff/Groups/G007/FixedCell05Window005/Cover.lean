import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node008_checked : node008.Check nodeSource008 targets := by
  refine ⟨node009_checked, ?_⟩
  have he : baselineFlip ⟨(-8234374999983/17128906250000), (1844015624996193/2192500000000000), (217020873613139660031088077/438500000000000000000000000)⟩ :: nodeSource008 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource008, nodeSource010]
  change node010.Check (baselineFlip ⟨(-8234374999983/17128906250000), (1844015624996193/2192500000000000), (217020873613139660031088077/438500000000000000000000000)⟩ :: nodeSource008) targets
  rw [he]
  exact node010_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-1844015624996193/2192500000000000), (-8234374999983/17128906250000), (-828976418065175861689313523/438500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-1844015624996193/2192500000000000), (-8234374999983/17128906250000), (-828976418065175861689313523/438500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-4430007359456848101490448412585945955508132825015574999/33501400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(271547787616447883460524677473/3820000000000000000000000000000), (-198113845557951435297917178449/955000000000000000000000000000), (-4430007359456848101490448412585945955508132825015574999/33501400000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(2176/4385), (-3807/4385), (-622295103050213874769199/2740625000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(2176/4385), (-3807/4385), (-622295103050213874769199/2740625000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-3807/4385), (-2176/4385), (-31339208229648013235219267367640193/16750700000000000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-3807/4385), (-2176/4385), (-31339208229648013235219267367640193/16750700000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window005
