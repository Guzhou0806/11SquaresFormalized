import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node004_checked : node004.Check nodeSource004 targets := by
  refine ⟨node005_checked, ?_⟩
  have he : baselineFlip ⟨(-2944/4625), (3567/4625), (2196111745403793125601743/2890625000000000000000000)⟩ :: nodeSource004 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource004, nodeSource006]
  change node006.Check (baselineFlip ⟨(-2944/4625), (3567/4625), (2196111745403793125601743/2890625000000000000000000)⟩ :: nodeSource004) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-11140624999977/18066406250000), (1727765624996433/2312500000000000), (8981326009672346783085929008405007730210317841/8833750000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(-11140624999977/18066406250000), (1727765624996433/2312500000000000), (8981326009672346783085929008405007730210317841/8833750000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-1727765624996433/2312500000000000), (-11140624999977/18066406250000), (-166846844481135984360139257033417270673286979/69013671875000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(-1727765624996433/2312500000000000), (-11140624999977/18066406250000), (-166846844481135984360139257033417270673286979/69013671875000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window005
