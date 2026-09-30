import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window037.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window037.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window037.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window037.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window037
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-21978237499954444389/135354213700000000000), (-10057837499979152517/10574547945312500000), (-496047723315321869158203471778063698327/522554568349836500000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-21978237499954444389/135354213700000000000), (-10057837499979152517/10574547945312500000), (-496047723315321869158203471778063698327/522554568349836500000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(1728/1753), (-295/1753), (2377948807075339045640357862458654220453/1034106192668000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(1728/1753), (-295/1753), (2377948807075339045640357862458654220453/1034106192668000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(295/1753), (1728/1753), (8603281026680083547410286558551448551/5049346643886718750000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(295/1753), (1728/1753), (8603281026680083547410286558551448551/5049346643886718750000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window037
