import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-480/481), (31/481), (-43978718509834462160984076364243/35335000000000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-480/481), (31/481), (-43978718509834462160984076364243/35335000000000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-1312499999997/1503125000000), (13562499999969/240500000000000), (-225463037839945093413507519/240500000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(-1312499999997/1503125000000), (13562499999969/240500000000000), (-225463037839945093413507519/240500000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(13562499999969/240500000000000), (1312499999997/1503125000000), (308494113902146933096793481/240500000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(13562499999969/240500000000000), (1312499999997/1503125000000), (308494113902146933096793481/240500000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(1312499999997/1503125000000), (-13562499999969/240500000000000), (409595850339103343413508481/240500000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(1312499999997/1503125000000), (-13562499999969/240500000000000), (409595850339103343413508481/240500000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window013
