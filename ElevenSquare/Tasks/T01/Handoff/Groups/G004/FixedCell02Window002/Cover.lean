import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window002.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window002.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window002.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (3183289029248583817842536309901070353660032549106516676513199417782867356793/3299556465798999694160000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (3183289029248583817842536309901070353660032549106516676513199417782867356793/3299556465798999694160000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(262119/262169), (5120/262169), (10675477842361057844572982942504526216657443959/4318791185600784940000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(262119/262169), (5120/262169), (10675477842361057844572982942504526216657443959/4318791185600784940000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window002
