import ElevenSquare.Tasks.T01.SymbolicWallDominance
import ElevenSquare.Tasks.T01.HalfTurnOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxHeartbeats 0

def ownedP005 : QPoint := (1603637329/1000000000, 63990253/100000000)
def ownedP006 : QPoint := (1572048057/1000000000, 232270007/250000000)
def ownedP007 : QPoint := (1543883109/1000000000, 339364257/500000000)
def ownedP008 : QPoint := (1543883109/1000000000, 629214151/1000000000)
def originalP14_005 : QPoint := (2333200481/1000000000, 799588769/250000000)
def mirrorP14_005 : QPoint := (154388310902281417731/100000000000000000000, 67872851402281417731/100000000000000000000)
theorem mirrorP14_005_eq : mirrorP14_005 = reflectQPoint originalP14_005 := by
  norm_num [mirrorP14_005, originalP14_005,
    reflectQPoint, baselineRationalCap]
def originalP14_006 : QPoint := (2333200481/1000000000, 3247869439/1000000000)
def mirrorP14_006 : QPoint := (154388310902281417731/100000000000000000000, 62921415102281417731/100000000000000000000)
theorem mirrorP14_006_eq : mirrorP14_006 = reflectQPoint originalP14_006 := by
  norm_num [mirrorP14_006, originalP14_006,
    reflectQPoint, baselineRationalCap]
def originalP14_008 : QPoint := (2273446261/1000000000, 161859053/50000000)
def mirrorP14_008 : QPoint := (160363732902281417731/100000000000000000000, 63990253002281417731/100000000000000000000)
theorem mirrorP14_008_eq : mirrorP14_008 = reflectQPoint originalP14_008 := by
  norm_num [mirrorP14_008, originalP14_008,
    reflectQPoint, baselineRationalCap]
def originalP14_009 : QPoint := (2305035533/1000000000, 1474001781/500000000)
def mirrorP14_009 : QPoint := (157204805702281417731/100000000000000000000, 92908002802281417731/100000000000000000000)
theorem mirrorP14_009_eq : mirrorP14_009 = reflectQPoint originalP14_009 := by
  norm_num [mirrorP14_009, originalP14_009,
    reflectQPoint, baselineRationalCap]

def points : List QPoint := [ownedP005, ownedP006, ownedP007, ownedP008, mirrorP14_005, mirrorP14_006, mirrorP14_008, mirrorP14_009]

def facet001 : SymbolicWallFacet := ⟨1, 0, 387708359002281417731/100000000000000000000, -1⟩
theorem facet001_mem : facet001 ∈ symbolicWallSlab 1 := by
  norm_num [symbolicWallSlab, DiskCell01.source_matches,
    DiskCell01.source, SymbolicWallFacet.ofHalfplane,
    facet001, baselineRationalCap]

def facet002 : SymbolicWallFacet := ⟨0, -1, 0, -1⟩
theorem facet002_mem : facet002 ∈ symbolicWallSlab 1 := by
  norm_num [symbolicWallSlab, DiskCell01.source_matches,
    DiskCell01.source, SymbolicWallFacet.ofHalfplane,
    facet002, baselineRationalCap]

def facet008 : SymbolicWallFacet := ⟨-268211/500000, 174831/1000000, -201970885552390045307244760797429/400000000000000000000000000000000, 0⟩
theorem facet008_mem : facet008 ∈ symbolicWallSlab 1 := by
  norm_num [symbolicWallSlab, DiskCell01.source_matches,
    DiskCell01.source, SymbolicWallFacet.ofHalfplane,
    facet008, baselineRationalCap]

def facet010 : SymbolicWallFacet := ⟨520839/1000000, 93253/500000, 462987898199336901251185345901871/400000000000000000000000000000000, 0⟩
theorem facet010_mem : facet010 ∈ symbolicWallSlab 1 := by
  norm_num [symbolicWallSlab, DiskCell01.source_matches,
    DiskCell01.source, SymbolicWallFacet.ofHalfplane,
    facet010, baselineRationalCap]

def facet013 : SymbolicWallFacet := ⟨-4093/1000000, 26743/50000, 8588608573212199176944164507707/16000000000000000000000000000000, 0⟩
theorem facet013_mem : facet013 ∈ symbolicWallSlab 1 := by
  norm_num [symbolicWallSlab, DiskCell01.source_matches,
    DiskCell01.source, SymbolicWallFacet.ofHalfplane,
    facet013, baselineRationalCap]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01
