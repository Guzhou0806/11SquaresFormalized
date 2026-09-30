import ElevenSquare.Tasks.T01.SymbolicWallDominance
import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def ownedP005 : QPoint := (294604953/125000000, 249496063/250000000)
def ownedP006 : QPoint := (1119317069/500000000, 249496063/250000000)
def ownedP007 : QPoint := (559224399/250000000, 1943513/1953125)
def ownedP008 : QPoint := (561353533/250000000, 6081077/6250000)
def ownedP009 : QPoint := (2265303257/1000000000, 930682669/1000000000)
def originalP13_005 : QPoint := (820092997/500000000, 1441002467/500000000)
def mirrorP13_005 : QPoint := (223689759602281417731/100000000000000000000, 99507865602281417731/100000000000000000000)
theorem mirrorP13_005_eq : mirrorP13_005 = reflectQPoint originalP13_005 := by
  norm_num [mirrorP13_005, originalP13_005,
    reflectQPoint, baselineRationalCap]
def originalP13_006 : QPoint := (815834729/500000000, 290411127/100000000)
def mirrorP13_006 : QPoint := (224541413202281417731/100000000000000000000, 97297232002281417731/100000000000000000000)
theorem mirrorP13_006_eq : mirrorP13_006 = reflectQPoint originalP13_006 := by
  norm_num [mirrorP13_006, originalP13_006,
    reflectQPoint, baselineRationalCap]
def originalP13_007 : QPoint := (1611780333/1000000000, 2946400921/1000000000)
def mirrorP13_007 : QPoint := (226530325702281417731/100000000000000000000, 93068266902281417731/100000000000000000000)
theorem mirrorP13_007_eq : mirrorP13_007 = reflectQPoint originalP13_007 := by
  norm_num [mirrorP13_007, originalP13_007,
    reflectQPoint, baselineRationalCap]
def originalP13_010 : QPoint := (760121983/500000000, 1439549669/500000000)
def mirrorP13_010 : QPoint := (235683962402281417731/100000000000000000000, 99798425202281417731/100000000000000000000)
theorem mirrorP13_010_eq : mirrorP13_010 = reflectQPoint originalP13_010 := by
  norm_num [mirrorP13_010, originalP13_010,
    reflectQPoint, baselineRationalCap]
def originalP13_011 : QPoint := (409612363/250000000, 1439549669/500000000)
def mirrorP13_011 : QPoint := (223863413802281417731/100000000000000000000, 99798425202281417731/100000000000000000000)
theorem mirrorP13_011_eq : mirrorP13_011 = reflectQPoint originalP13_011 := by
  norm_num [mirrorP13_011, originalP13_011,
    reflectQPoint, baselineRationalCap]

def points : List QPoint := [ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, mirrorP13_005, mirrorP13_006, mirrorP13_007, mirrorP13_010, mirrorP13_011]

def facet000 : SymbolicWallFacet := ⟨-1, 0, 0, -1⟩
theorem facet000_mem : facet000 ∈ symbolicWallSlab 2 := by
  norm_num [symbolicWallSlab, DiskCell02.source_matches,
    DiskCell02.source, SymbolicWallFacet.ofHalfplane,
    facet000, baselineRationalCap]

def facet002 : SymbolicWallFacet := ⟨0, -1, 0, -1⟩
theorem facet002_mem : facet002 ∈ symbolicWallSlab 2 := by
  norm_num [symbolicWallSlab, DiskCell02.source_matches,
    DiskCell02.source, SymbolicWallFacet.ofHalfplane,
    facet002, baselineRationalCap]

def facet009 : SymbolicWallFacet := ⟨-520839/1000000, -93253/500000, -462987898199336901251185345901871/400000000000000000000000000000000, 0⟩
theorem facet009_mem : facet009 ∈ symbolicWallSlab 2 := by
  norm_num [symbolicWallSlab, DiskCell02.source_matches,
    DiskCell02.source, SymbolicWallFacet.ofHalfplane,
    facet009, baselineRationalCap]

def facet011 : SymbolicWallFacet := ⟨11597/25000, -2247/31250, 1171422739114251067047341103669/1000000000000000000000000000000, 0⟩
theorem facet011_mem : facet011 ∈ symbolicWallSlab 2 := by
  norm_num [symbolicWallSlab, DiskCell02.source_matches,
    DiskCell02.source, SymbolicWallFacet.ofHalfplane,
    facet011, baselineRationalCap]

def facet013 : SymbolicWallFacet := ⟨-131233/250000, 174177/500000, -62068170967257980456895308302299/100000000000000000000000000000000, 0⟩
theorem facet013_mem : facet013 ∈ symbolicWallSlab 2 := by
  norm_num [symbolicWallSlab, DiskCell02.source_matches,
    DiskCell02.source, SymbolicWallFacet.ofHalfplane,
    facet013, baselineRationalCap]

def facet014 : SymbolicWallFacet := ⟨3271/1000000, 554533/1000000, 72742996320125630358412383355367/100000000000000000000000000000000, 0⟩
theorem facet014_mem : facet014 ∈ symbolicWallSlab 2 := by
  norm_num [symbolicWallSlab, DiskCell02.source_matches,
    DiskCell02.source, SymbolicWallFacet.ofHalfplane,
    facet014, baselineRationalCap]

def facet015 : SymbolicWallFacet := ⟨514513/1000000, 19677/50000, 740353899055297055471770031402357/400000000000000000000000000000000, 0⟩
theorem facet015_mem : facet015 ∈ symbolicWallSlab 2 := by
  norm_num [symbolicWallSlab, DiskCell02.source_matches,
    DiskCell02.source, SymbolicWallFacet.ofHalfplane,
    facet015, baselineRationalCap]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02
