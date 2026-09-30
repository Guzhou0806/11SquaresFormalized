import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window032.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window032.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window032.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window032.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window032
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(92726068460142313087578812611/955000000000000000000000000000), (2489668839624791121678198769/764000000000000000000000000000), (6895805925436398836513000357826451864807773676098756065489665699889/26367745935440000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(92726068460142313087578812611/955000000000000000000000000000), (2489668839624791121678198769/764000000000000000000000000000), (6895805925436398836513000357826451864807773676098756065489665699889/26367745935440000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(1088/1313), (-735/1313), (437141856902000462757969557659171427/269630909843750000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(1088/1313), (-735/1313), (437141856902000462757969557659171427/269630909843750000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(735/1313), (1088/1313), (106421008917564067560603240943/45173765000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(735/1313), (1088/1313), (106421008917564067560603240943/45173765000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window032
