import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.CoverLeaf009
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.CoverLeaf010

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node008_checked : node008.Check nodeSource008 targets := by
  refine ⟨node009_checked, ?_⟩
  have he : baselineFlip ⟨(-1600/1649), (399/1649), (-875036912836022431311693/1030625000000000000000000)⟩ :: nodeSource008 = nodeSource010 := by
    norm_num [baselineFlip, nodeSource008, nodeSource010]
  change node010.Check (baselineFlip ⟨(-1600/1649), (399/1649), (-875036912836022431311693/1030625000000000000000000)⟩ :: nodeSource008) targets
  rw [he]
  exact node010_checked

theorem node005_checked : node005.Check nodeSource005 targets := by
  refine ⟨node006_checked, ?_⟩
  have he : baselineFlip ⟨(-468749999999/515312500000), (187031249999601/824500000000000), (-543343382170863836201366351/824500000000000000000000000)⟩ :: nodeSource005 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource005, nodeSource007]
  change node007.Check (baselineFlip ⟨(-468749999999/515312500000), (187031249999601/824500000000000), (-543343382170863836201366351/824500000000000000000000000)⟩ :: nodeSource005) targets
  rw [he]
  exact node007_checked

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(187031249999601/824500000000000), (468749999999/515312500000), (1719573980272746106758743649/824500000000000000000000000)⟩ :: nodeSource004 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource004, nodeSource008]
  change node008.Check (baselineFlip ⟨(187031249999601/824500000000000), (468749999999/515312500000), (1719573980272746106758743649/824500000000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node008_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-468749999999/515312500000), (187031249999601/824500000000000), (-2503197145717848310898821910752988946251558223/3149590000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-468749999999/515312500000), (187031249999601/824500000000000), (-2503197145717848310898821910752988946251558223/3149590000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-187031249999601/824500000000000), (-468749999999/515312500000), (-4177582472989796802369563063590694901339923/1968493750000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-187031249999601/824500000000000), (-468749999999/515312500000), (-4177582472989796802369563063590694901339923/1968493750000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020
