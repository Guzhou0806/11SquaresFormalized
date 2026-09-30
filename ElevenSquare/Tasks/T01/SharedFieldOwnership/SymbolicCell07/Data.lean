import ElevenSquare.Tasks.T01.SymbolicWallDominance
import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell07.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def ownedP006 : QPoint := (1533873877/500000000, 1486952043/1000000000)
def ownedP007 : QPoint := (3047858629/1000000000, 305848339/200000000)
def ownedP008 : QPoint := (3018841763/1000000000, 1554336589/1000000000)
def ownedP009 : QPoint := (728792327/250000000, 1520103527/1000000000)
def ownedP010 : QPoint := (180050283/62500000, 1504634021/1000000000)
def ownedP011 : QPoint := (180050283/62500000, 1448584901/1000000000)
def ownedP012 : QPoint := (2944795153/1000000000, 1418113041/1000000000)
def ownedP013 : QPoint := (2993103927/1000000000, 1399934221/1000000000)
def ownedP014 : QPoint := (1486197139/500000000, 1541873753/1000000000)
def originalP08_005 : QPoint := (498139531/500000000, 2372449569/1000000000)
def mirrorP08_005 : QPoint := (288080452802281417731/100000000000000000000, 150463402102281417731/100000000000000000000)
theorem mirrorP08_005_eq : mirrorP08_005 = reflectQPoint originalP08_005 := by
  norm_num [mirrorP08_005, originalP08_005,
    reflectQPoint, baselineRationalCap]
def originalP08_006 : QPoint := (498139531/500000000, 2428498689/1000000000)
def mirrorP08_006 : QPoint := (288080452802281417731/100000000000000000000, 144858490102281417731/100000000000000000000)
theorem mirrorP08_006_eq : mirrorP08_006 = reflectQPoint originalP08_006 := by
  norm_num [mirrorP08_006, originalP08_006,
    reflectQPoint, baselineRationalCap]
def originalP08_007 : QPoint := (932288437/1000000000, 2458970549/1000000000)
def mirrorP08_007 : QPoint := (294479515302281417731/100000000000000000000, 141811304102281417731/100000000000000000000)
theorem mirrorP08_007_eq : mirrorP08_007 = reflectQPoint originalP08_007 := by
  norm_num [mirrorP08_007, originalP08_007,
    reflectQPoint, baselineRationalCap]
def originalP08_008 : QPoint := (883979663/1000000000, 2477149369/1000000000)
def mirrorP08_008 : QPoint := (299310392702281417731/100000000000000000000, 139993422102281417731/100000000000000000000)
theorem mirrorP08_008_eq : mirrorP08_008 = reflectQPoint originalP08_008 := by
  norm_num [mirrorP08_008, originalP08_008,
    reflectQPoint, baselineRationalCap]
def originalP08_010 : QPoint := (202333959/250000000, 2390131547/1000000000)
def mirrorP08_010 : QPoint := (306774775402281417731/100000000000000000000, 148695204302281417731/100000000000000000000)
theorem mirrorP08_010_eq : mirrorP08_010 = reflectQPoint originalP08_010 := by
  norm_num [mirrorP08_010, originalP08_010,
    reflectQPoint, baselineRationalCap]
def originalP08_011 : QPoint := (829224961/1000000000, 293480237/125000000)
def mirrorP08_011 : QPoint := (304785862902281417731/100000000000000000000, 152924169402281417731/100000000000000000000)
theorem mirrorP08_011_eq : mirrorP08_011 = reflectQPoint originalP08_011 := by
  norm_num [mirrorP08_011, originalP08_011,
    reflectQPoint, baselineRationalCap]
def originalP08_012 : QPoint := (858241827/1000000000, 1161373501/500000000)
def mirrorP08_012 : QPoint := (301884176302281417731/100000000000000000000, 155433658802281417731/100000000000000000000)
theorem mirrorP08_012_eq : mirrorP08_012 = reflectQPoint originalP08_012 := by
  norm_num [mirrorP08_012, originalP08_012,
    reflectQPoint, baselineRationalCap]
def originalP08_013 : QPoint := (480957141/500000000, 2356980063/1000000000)
def mirrorP08_013 : QPoint := (291516930802281417731/100000000000000000000, 152010352702281417731/100000000000000000000)
theorem mirrorP08_013_eq : mirrorP08_013 = reflectQPoint originalP08_013 := by
  norm_num [mirrorP08_013, originalP08_013,
    reflectQPoint, baselineRationalCap]

def points : List QPoint := [ownedP006, ownedP007, ownedP008, ownedP009, ownedP010, ownedP011, ownedP012, ownedP013, ownedP014, mirrorP08_005, mirrorP08_006, mirrorP08_007, mirrorP08_008, mirrorP08_010, mirrorP08_011, mirrorP08_012, mirrorP08_013]

def facet001 : SymbolicWallFacet := ⟨1, 0, 387708359002281417731/100000000000000000000, -1⟩
theorem facet001_mem : facet001 ∈ symbolicWallSlab 7 := by
  norm_num [symbolicWallSlab, DiskCell07.source_matches,
    DiskCell07.source, SymbolicWallFacet.ofHalfplane,
    facet001, baselineRationalCap]

def facet008 : SymbolicWallFacet := ⟨-785887/500000, -81043/200000, -1405312682807024002030200138101657/400000000000000000000000000000000, 0⟩
theorem facet008_mem : facet008 ∈ symbolicWallSlab 7 := by
  norm_num [symbolicWallSlab, DiskCell07.source_matches,
    DiskCell07.source, SymbolicWallFacet.ofHalfplane,
    facet008, baselineRationalCap]

def facet010 : SymbolicWallFacet := ⟨-514513/1000000, -19677/50000, -740353899055297055471770031402357/400000000000000000000000000000000, 0⟩
theorem facet010_mem : facet010 ∈ symbolicWallSlab 7 := by
  norm_num [symbolicWallSlab, DiskCell07.source_matches,
    DiskCell07.source, SymbolicWallFacet.ofHalfplane,
    facet010, baselineRationalCap]

def facet011 : SymbolicWallFacet := ⟨-50633/1000000, -116361/250000, -271784803409596628652833589934757/400000000000000000000000000000000, 0⟩
theorem facet011_mem : facet011 ∈ symbolicWallSlab 7 := by
  norm_num [symbolicWallSlab, DiskCell07.source_matches,
    DiskCell07.source, SymbolicWallFacet.ofHalfplane,
    facet011, baselineRationalCap]

def facet014 : SymbolicWallFacet := ⟨-255621/500000, 160993/1000000, -449381913774794534038120497980889/400000000000000000000000000000000, 0⟩
theorem facet014_mem : facet014 ∈ symbolicWallSlab 7 := by
  norm_num [symbolicWallSlab, DiskCell07.source_matches,
    DiskCell07.source, SymbolicWallFacet.ofHalfplane,
    facet014, baselineRationalCap]

def facet019 : SymbolicWallFacet := ⟨12063/1000000, 52819/100000, 80935741813217249893494452605227/80000000000000000000000000000000, 0⟩
theorem facet019_mem : facet019 ∈ symbolicWallSlab 7 := by
  norm_num [symbolicWallSlab, DiskCell07.source_matches,
    DiskCell07.source, SymbolicWallFacet.ofHalfplane,
    facet019, baselineRationalCap]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07
