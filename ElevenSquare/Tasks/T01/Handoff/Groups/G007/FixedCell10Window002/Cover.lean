import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-1312499999997/4140625000000), (108062499999753/132500000000000), (34272677767460974950817053/26500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-1312499999997/4140625000000), (108062499999753/132500000000000), (34272677767460974950817053/26500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-1312499999997/4140625000000), (108062499999753/132500000000000), (845681482491795872647354088327882224694273481/506150000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(-1312499999997/4140625000000), (108062499999753/132500000000000), (845681482491795872647354088327882224694273481/506150000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(108062499999753/132500000000000), (1312499999997/4140625000000), (42757765110695343033884096121663416953207269/15817187500000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(108062499999753/132500000000000), (1312499999997/4140625000000), (42757765110695343033884096121663416953207269/15817187500000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(1312499999997/4140625000000), (-108062499999753/132500000000000), (-458160388743567397647352063727882224694273481/506150000000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(1312499999997/4140625000000), (-108062499999753/132500000000000), (-458160388743567397647352063727882224694273481/506150000000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window002
