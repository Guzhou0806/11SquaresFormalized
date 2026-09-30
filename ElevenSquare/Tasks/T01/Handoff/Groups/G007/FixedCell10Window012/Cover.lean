import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(164203124999661/649700000000000), (23734374999951/25378906250000), (10683359232469015798177276497/3248500000000000000000000000)⟩ :: nodeSource004 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource004, nodeSource006]
  change node006.Check (baselineFlip ⟨(164203124999661/649700000000000), (23734374999951/25378906250000), (10683359232469015798177276497/3248500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(164203124999661/649700000000000), (23734374999951/25378906250000), (304486010245397395266978766169470202961499977/96947421875000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(164203124999661/649700000000000), (23734374999951/25378906250000), (304486010245397395266978766169470202961499977/96947421875000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(23734374999951/25378906250000), (-164203124999661/649700000000000), (4200791017414637564382075584110236946888203603/2481854000000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(23734374999951/25378906250000), (-164203124999661/649700000000000), (4200791017414637564382075584110236946888203603/2481854000000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window012
