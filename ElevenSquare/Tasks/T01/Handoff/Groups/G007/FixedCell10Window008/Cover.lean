import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(1406249999997/1951562500000), (-374531249999201/624500000000000), (207585007331159183234359249/624500000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(1406249999997/1951562500000), (-374531249999201/624500000000000), (207585007331159183234359249/624500000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(374531249999201/624500000000000), (1406249999997/1951562500000), (24474302374047050723688486166784524356644769/7454968750000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(374531249999201/624500000000000), (1406249999997/1951562500000), (24474302374047050723688486166784524356644769/7454968750000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(1406249999997/1951562500000), (-374531249999201/624500000000000), (1043275455698075156094795169974208185240589023/2385590000000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(1406249999997/1951562500000), (-374531249999201/624500000000000), (1043275455698075156094795169974208185240589023/2385590000000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008
