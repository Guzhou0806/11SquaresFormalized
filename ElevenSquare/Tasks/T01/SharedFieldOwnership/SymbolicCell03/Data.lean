import ElevenSquare.Tasks.T01.SymbolicWallDominance
import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def ownedP005 : QPoint := (1537998631/500000000, 830458721/1000000000)
def ownedP006 : QPoint := (3033327231/1000000000, 486019933/500000000)
def ownedP007 : QPoint := (1511413727/500000000, 497957757/500000000)
def ownedP008 : QPoint := (1439673887/500000000, 497957757/500000000)
def ownedP009 : QPoint := (1439673887/500000000, 359788647/500000000)
def ownedP010 : QPoint := (1451239527/500000000, 706762123/1000000000)
def ownedP011 : QPoint := (3058261939/1000000000, 40587311/50000000)
def originalP12_005 : QPoint := (124716977/125000000, 720292019/250000000)
def mirrorP12_005 : QPoint := (287934777402281417731/100000000000000000000, 99591551402281417731/100000000000000000000)
theorem mirrorP12_005_eq : mirrorP12_005 = reflectQPoint originalP12_005 := by
  norm_num [mirrorP12_005, originalP12_005,
    reflectQPoint, baselineRationalCap]
def originalP12_006 : QPoint := (124716977/125000000, 394688287/125000000)
def mirrorP12_006 : QPoint := (287934777402281417731/100000000000000000000, 71957729402281417731/100000000000000000000)
theorem mirrorP12_006_eq : mirrorP12_006 = reflectQPoint originalP12_006 := by
  norm_num [mirrorP12_006, originalP12_006,
    reflectQPoint, baselineRationalCap]
def originalP12_007 : QPoint := (121825567/125000000, 3170321467/1000000000)
def mirrorP12_007 : QPoint := (290247905402281417731/100000000000000000000, 70676212302281417731/100000000000000000000)
theorem mirrorP12_007_eq : mirrorP12_007 = reflectQPoint originalP12_007 := by
  norm_num [mirrorP12_007, originalP12_007,
    reflectQPoint, baselineRationalCap]
def originalP12_008 : QPoint := (818821651/1000000000, 306533737/100000000)
def mirrorP12_008 : QPoint := (305826193902281417731/100000000000000000000, 81174622002281417731/100000000000000000000)
theorem mirrorP12_008_eq : mirrorP12_008 = reflectQPoint originalP12_008 := by
  norm_num [mirrorP12_008, originalP12_008,
    reflectQPoint, baselineRationalCap]
def originalP12_009 : QPoint := (100135791/125000000, 3046624869/1000000000)
def mirrorP12_009 : QPoint := (307599726202281417731/100000000000000000000, 83045872102281417731/100000000000000000000)
theorem mirrorP12_009_eq : mirrorP12_009 = reflectQPoint originalP12_009 := by
  norm_num [mirrorP12_009, originalP12_009,
    reflectQPoint, baselineRationalCap]
def originalP12_010 : QPoint := (843756359/1000000000, 726260931/250000000)
def mirrorP12_010 : QPoint := (303332723102281417731/100000000000000000000, 97203986602281417731/100000000000000000000)
theorem mirrorP12_010_eq : mirrorP12_010 = reflectQPoint originalP12_010 := by
  norm_num [mirrorP12_010, originalP12_010,
    reflectQPoint, baselineRationalCap]
def originalP12_011 : QPoint := (106782017/125000000, 720292019/250000000)
def mirrorP12_011 : QPoint := (302282745402281417731/100000000000000000000, 99591551402281417731/100000000000000000000)
theorem mirrorP12_011_eq : mirrorP12_011 = reflectQPoint originalP12_011 := by
  norm_num [mirrorP12_011, originalP12_011,
    reflectQPoint, baselineRationalCap]

def points : List QPoint := [ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, ownedP010, ownedP011, mirrorP12_005, mirrorP12_006, mirrorP12_007, mirrorP12_008, mirrorP12_009, mirrorP12_010, mirrorP12_011]

def facet001 : SymbolicWallFacet := ⟨1, 0, 387708359002281417731/100000000000000000000, -1⟩
theorem facet001_mem : facet001 ∈ symbolicWallSlab 3 := by
  norm_num [symbolicWallSlab, DiskCell03.source_matches,
    DiskCell03.source, SymbolicWallFacet.ofHalfplane,
    facet001, baselineRationalCap]

def facet002 : SymbolicWallFacet := ⟨0, -1, 0, -1⟩
theorem facet002_mem : facet002 ∈ symbolicWallSlab 3 := by
  norm_num [symbolicWallSlab, DiskCell03.source_matches,
    DiskCell03.source, SymbolicWallFacet.ofHalfplane,
    facet002, baselineRationalCap]

def facet010 : SymbolicWallFacet := ⟨-11597/25000, 2247/31250, -1171422739114251067047341103669/1000000000000000000000000000000, 0⟩
theorem facet010_mem : facet010 ∈ symbolicWallSlab 3 := by
  norm_num [symbolicWallSlab, DiskCell03.source_matches,
    DiskCell03.source, SymbolicWallFacet.ofHalfplane,
    facet010, baselineRationalCap]

def facet015 : SymbolicWallFacet := ⟨50633/1000000, 116361/250000, 271784803409596628652833589934757/400000000000000000000000000000000, 0⟩
theorem facet015_mem : facet015 ∈ symbolicWallSlab 3 := by
  norm_num [symbolicWallSlab, DiskCell03.source_matches,
    DiskCell03.source, SymbolicWallFacet.ofHalfplane,
    facet015, baselineRationalCap]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03
