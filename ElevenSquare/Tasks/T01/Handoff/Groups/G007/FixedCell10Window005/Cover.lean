import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005.CoverLeaf006

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(11140624999977/18066406250000), (-1727765624996433/2312500000000000), (-5770920170826257717227947/18500000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(11140624999977/18066406250000), (-1727765624996433/2312500000000000), (-5770920170826257717227947/18500000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(1727765624996433/2312500000000000), (11140624999977/18066406250000), (231614558027621486069123908088104770673286979/69013671875000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(1727765624996433/2312500000000000), (11140624999977/18066406250000), (231614558027621486069123908088104770673286979/69013671875000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(11140624999977/18066406250000), (-1727765624996433/2312500000000000), (-691058675722202564335893673405007730210317841/8833750000000000000000000000000000000000000000)⟩ :: nodeSource000 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource000, nodeSource006]
  change node006.Check (baselineFlip ⟨(11140624999977/18066406250000), (-1727765624996433/2312500000000000), (-691058675722202564335893673405007730210317841/8833750000000000000000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node006_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window005
