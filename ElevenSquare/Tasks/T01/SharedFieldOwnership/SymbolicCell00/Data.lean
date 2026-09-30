import ElevenSquare.Tasks.T01.SymbolicWallDominance
import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def ownedP005 : QPoint := (498020679/500000000, 872404559/1000000000)
def ownedP006 : QPoint := (498020679/500000000, 997648353/1000000000)
def ownedP007 : QPoint := (386169321/500000000, 997648353/1000000000)
def ownedP009 : QPoint := (175226227/200000000, 410961817/500000000)
def ownedP010 : QPoint := (37415093/40000000, 843701669/1000000000)
def originalP15_005 : QPoint := (776186237/250000000, 2879435237/1000000000)
def mirrorP15_005 : QPoint := (77233864202281417731/100000000000000000000, 99764835302281417731/100000000000000000000)
theorem mirrorP15_005_eq : mirrorP15_005 = reflectQPoint originalP15_005 := by
  norm_num [mirrorP15_005, originalP15_005,
    reflectQPoint, baselineRationalCap]
def originalP15_007 : QPoint := (600190491/200000000, 763789989/250000000)
def mirrorP15_007 : QPoint := (87613113502281417731/100000000000000000000, 82192363402281417731/100000000000000000000)
theorem mirrorP15_007_eq : mirrorP15_007 = reflectQPoint originalP15_007 := by
  norm_num [mirrorP15_007, originalP15_007,
    reflectQPoint, baselineRationalCap]
def originalP15_008 : QPoint := (588341253/200000000, 3033381921/1000000000)
def mirrorP15_008 : QPoint := (93537732502281417731/100000000000000000000, 84370166902281417731/100000000000000000000)
theorem mirrorP15_008_eq : mirrorP15_008 = reflectQPoint originalP15_008 := by
  norm_num [mirrorP15_008, originalP15_008,
    reflectQPoint, baselineRationalCap]
def originalP15_009 : QPoint := (360130279/125000000, 3004679031/1000000000)
def mirrorP15_009 : QPoint := (99604135802281417731/100000000000000000000, 87240455902281417731/100000000000000000000)
theorem mirrorP15_009_eq : mirrorP15_009 = reflectQPoint originalP15_009 := by
  norm_num [mirrorP15_009, originalP15_009,
    reflectQPoint, baselineRationalCap]
def originalP15_010 : QPoint := (360130279/125000000, 2879435237/1000000000)
def mirrorP15_010 : QPoint := (99604135802281417731/100000000000000000000, 99764835302281417731/100000000000000000000)
theorem mirrorP15_010_eq : mirrorP15_010 = reflectQPoint originalP15_010 := by
  norm_num [mirrorP15_010, originalP15_010,
    reflectQPoint, baselineRationalCap]

def points : List QPoint := [ownedP005, ownedP006, ownedP007, ownedP009, ownedP010, mirrorP15_005, mirrorP15_007, mirrorP15_008, mirrorP15_009, mirrorP15_010]

def facet000 : SymbolicWallFacet := ⟨-1, 0, 0, -1⟩
theorem facet000_mem : facet000 ∈ symbolicWallSlab 0 := by
  norm_num [symbolicWallSlab, DiskCell00.source_matches,
    DiskCell00.source, SymbolicWallFacet.ofHalfplane,
    facet000, baselineRationalCap]

def facet001 : SymbolicWallFacet := ⟨1, 0, 387708359002281417731/100000000000000000000, -1⟩
theorem facet001_mem : facet001 ∈ symbolicWallSlab 0 := by
  norm_num [symbolicWallSlab, DiskCell00.source_matches,
    DiskCell00.source, SymbolicWallFacet.ofHalfplane,
    facet001, baselineRationalCap]

def facet002 : SymbolicWallFacet := ⟨0, -1, 0, -1⟩
theorem facet002_mem : facet002 ∈ symbolicWallSlab 0 := by
  norm_num [symbolicWallSlab, DiskCell00.source_matches,
    DiskCell00.source, SymbolicWallFacet.ofHalfplane,
    facet002, baselineRationalCap]

def facet009 : SymbolicWallFacet := ⟨268211/500000, -174831/1000000, 201970885552390045307244760797429/400000000000000000000000000000000, 0⟩
theorem facet009_mem : facet009 ∈ symbolicWallSlab 0 := by
  norm_num [symbolicWallSlab, DiskCell00.source_matches,
    DiskCell00.source, SymbolicWallFacet.ofHalfplane,
    facet009, baselineRationalCap]

def facet012 : SymbolicWallFacet := ⟨-3801/1000000, 534921/1000000, 16869949317278243975263377320487/25000000000000000000000000000000, 0⟩
theorem facet012_mem : facet012 ∈ symbolicWallSlab 0 := by
  norm_num [symbolicWallSlab, DiskCell00.source_matches,
    DiskCell00.source, SymbolicWallFacet.ofHalfplane,
    facet012, baselineRationalCap]

def facet013 : SymbolicWallFacet := ⟨532329/1000000, 360029/1000000, 52085762485336878091356109186263/50000000000000000000000000000000, 0⟩
theorem facet013_mem : facet013 ∈ symbolicWallSlab 0 := by
  norm_num [symbolicWallSlab, DiskCell00.source_matches,
    DiskCell00.source, SymbolicWallFacet.ofHalfplane,
    facet013, baselineRationalCap]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00
