import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (39881334923970214271161600302554048537948342071505582085005519397068993853/41478075795637321360000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource002, nodeSource004]
  change node004.Check (baselineFlip ⟨(228424430670553045862305177717/764000000000000000000000000000), (697303673804402786751705723873/3820000000000000000000000000000), (39881334923970214271161600302554048537948342071505582085005519397068993853/41478075795637321360000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node004_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(3584/65585), (-65487/65585), (-105744033310298939653742641278056963773685489/271453375625898700000000000000000000000000000)⟩ :: nodeSource001 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource001, nodeSource005]
  change node005.Check (baselineFlip ⟨(3584/65585), (-65487/65585), (-105744033310298939653742641278056963773685489/271453375625898700000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node005_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(65487/65585), (3584/65585), (679260105558493072490541796436734774094562623/271453375625898700000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(65487/65585), (3584/65585), (679260105558493072490541796436734774094562623/271453375625898700000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window005
