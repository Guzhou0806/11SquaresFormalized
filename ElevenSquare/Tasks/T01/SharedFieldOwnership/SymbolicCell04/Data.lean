import ElevenSquare.Tasks.T01.SymbolicWallDominance
import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def ownedP005 : QPoint := (248983/250000, 65635441/40000000)
def ownedP006 : QPoint := (248983/250000, 830121073/500000000)
def ownedP007 : QPoint := (469364497/500000000, 1687172101/1000000000)
def ownedP008 : QPoint := (868050603/1000000000, 1712569751/1000000000)
def ownedP010 : QPoint := (790375591/1000000000, 1630323183/1000000000)
def ownedP011 : QPoint := (857991217/1000000000, 1586351539/1000000000)
def ownedP012 : QPoint := (471031633/500000000, 807848477/500000000)
def originalP11_006 : QPoint := (3086707999/1000000000, 2246760407/1000000000)
def mirrorP11_006 : QPoint := (79037559102281417731/100000000000000000000, 163032318302281417731/100000000000000000000)
theorem mirrorP11_006_eq : mirrorP11_006 = reflectQPoint originalP11_006 := by
  norm_num [mirrorP11_006, originalP11_006,
    reflectQPoint, baselineRationalCap]
def originalP11_007 : QPoint := (3019092373/1000000000, 2290732051/1000000000)
def mirrorP11_007 : QPoint := (85799121702281417731/100000000000000000000, 158635153902281417731/100000000000000000000)
theorem mirrorP11_007_eq : mirrorP11_007 = reflectQPoint originalP11_007 := by
  norm_num [mirrorP11_007, originalP11_007,
    reflectQPoint, baselineRationalCap]
def originalP11_008 : QPoint := (733755081/250000000, 565346659/250000000)
def mirrorP11_008 : QPoint := (94206326602281417731/100000000000000000000, 161569695402281417731/100000000000000000000)
theorem mirrorP11_008_eq : mirrorP11_008 = reflectQPoint originalP11_008 := by
  norm_num [mirrorP11_008, originalP11_008,
    reflectQPoint, baselineRationalCap]
def originalP11_009 : QPoint := (288115159/100000000, 447239513/200000000)
def mirrorP11_009 : QPoint := (99593200002281417731/100000000000000000000, 164088602502281417731/100000000000000000000)
theorem mirrorP11_009_eq : mirrorP11_009 = reflectQPoint originalP11_009 := by
  norm_num [mirrorP11_009, originalP11_009,
    reflectQPoint, baselineRationalCap]
def originalP11_010 : QPoint := (288115159/100000000, 554210361/250000000)
def mirrorP11_010 : QPoint := (99593200002281417731/100000000000000000000, 166024214602281417731/100000000000000000000)
theorem mirrorP11_010_eq : mirrorP11_010 = reflectQPoint originalP11_010 := by
  norm_num [mirrorP11_010, originalP11_010,
    reflectQPoint, baselineRationalCap]
def originalP11_011 : QPoint := (734588649/250000000, 2189911489/1000000000)
def mirrorP11_011 : QPoint := (93872899402281417731/100000000000000000000, 168717210102281417731/100000000000000000000)
theorem mirrorP11_011_eq : mirrorP11_011 = reflectQPoint originalP11_011 := by
  norm_num [mirrorP11_011, originalP11_011,
    reflectQPoint, baselineRationalCap]
def originalP11_012 : QPoint := (752258247/250000000, 2164513839/1000000000)
def mirrorP11_012 : QPoint := (86805060202281417731/100000000000000000000, 171256975102281417731/100000000000000000000)
theorem mirrorP11_012_eq : mirrorP11_012 = reflectQPoint originalP11_012 := by
  norm_num [mirrorP11_012, originalP11_012,
    reflectQPoint, baselineRationalCap]
def originalP11_013 : QPoint := (1440671663/500000000, 2221138619/1000000000)
def mirrorP11_013 : QPoint := (99574026402281417731/100000000000000000000, 165594497102281417731/100000000000000000000)
theorem mirrorP11_013_eq : mirrorP11_013 = reflectQPoint originalP11_013 := by
  norm_num [mirrorP11_013, originalP11_013,
    reflectQPoint, baselineRationalCap]

def points : List QPoint := [ownedP005, ownedP006, ownedP007, ownedP008, ownedP010, ownedP011, ownedP012, mirrorP11_006, mirrorP11_007, mirrorP11_008, mirrorP11_009, mirrorP11_010, mirrorP11_011, mirrorP11_012, mirrorP11_013]

def facet000 : SymbolicWallFacet := ⟨-1, 0, 0, -1⟩
theorem facet000_mem : facet000 ∈ symbolicWallSlab 4 := by
  norm_num [symbolicWallSlab, DiskCell04.source_matches,
    DiskCell04.source, SymbolicWallFacet.ofHalfplane,
    facet000, baselineRationalCap]

def facet008 : SymbolicWallFacet := ⟨3801/1000000, -534921/1000000, -16869949317278243975263377320487/25000000000000000000000000000000, 0⟩
theorem facet008_mem : facet008 ∈ symbolicWallSlab 4 := by
  norm_num [symbolicWallSlab, DiskCell04.source_matches,
    DiskCell04.source, SymbolicWallFacet.ofHalfplane,
    facet008, baselineRationalCap]

def facet013 : SymbolicWallFacet := ⟨53613/100000, -43723/250000, 18345863850780390140829354545289/50000000000000000000000000000000, 0⟩
theorem facet013_mem : facet013 ∈ symbolicWallSlab 4 := by
  norm_num [symbolicWallSlab, DiskCell04.source_matches,
    DiskCell04.source, SymbolicWallFacet.ofHalfplane,
    facet013, baselineRationalCap]

def facet016 : SymbolicWallFacet := ⟨12063/1000000, 52819/100000, 86632741447630384325246301794773/80000000000000000000000000000000, 0⟩
theorem facet016_mem : facet016 ∈ symbolicWallSlab 4 := by
  norm_num [symbolicWallSlab, DiskCell04.source_matches,
    DiskCell04.source, SymbolicWallFacet.ofHalfplane,
    facet016, baselineRationalCap]

def facet017 : SymbolicWallFacet := ⟨104661/200000, 367197/1000000, 32934978349507352793973192937061/25000000000000000000000000000000, 0⟩
theorem facet017_mem : facet017 ∈ symbolicWallSlab 4 := by
  norm_num [symbolicWallSlab, DiskCell04.source_matches,
    DiskCell04.source, SymbolicWallFacet.ofHalfplane,
    facet017, baselineRationalCap]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04
