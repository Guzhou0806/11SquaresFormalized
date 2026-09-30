import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.CoverLeaf008
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node007_checked : node007.Check nodeSource007 targets := by
  refine ⟨node008_checked, ?_⟩
  have he : baselineFlip ⟨(-113581730769/132265625000), (407341947114557/846500000000000), (-145678309693162893071407307/846500000000000000000000000)⟩ :: nodeSource007 = nodeSource009 := by
    norm_num [baselineFlip, nodeSource007, nodeSource009]
  change node009.Check (baselineFlip ⟨(-113581730769/132265625000), (407341947114557/846500000000000), (-145678309693162893071407307/846500000000000000000000000)⟩ :: nodeSource007) targets
  rw [he]
  exact node009_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(407341947114557/846500000000000), (113581730769/132265625000), (2022679979296799943002601693/846500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(407341947114557/846500000000000), (113581730769/132265625000), (2022679979296799943002601693/846500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(113581730769/132265625000), (-407341947114557/846500000000000), (457806455429257012805679693/846500000000000000000000000)⟩ :: nodeSource004 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource004, nodeSource010]
  change node010.Check (baselineFlip ⟨(113581730769/132265625000), (-407341947114557/846500000000000), (457806455429257012805679693/846500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node010_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-113581730769/132265625000), (407341947114557/846500000000000), (-186540396376824749186457360041718280184996611/3233630000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-113581730769/132265625000), (407341947114557/846500000000000), (-186540396376824749186457360041718280184996611/3233630000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-407341947114557/846500000000000), (-113581730769/132265625000), (-619324893753996746490944393879161963381169/252627343750000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-407341947114557/846500000000000), (-113581730769/132265625000), (-619324893753996746490944393879161963381169/252627343750000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015
