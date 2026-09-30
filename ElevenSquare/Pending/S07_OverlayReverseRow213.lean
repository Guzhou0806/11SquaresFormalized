import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev213_planes : List IntegerPlane := integerOverlayPlanes ![15,8,13,10]
def rev213_plane14 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-2741459880216)⟩
theorem rev213_plane14_mem : rev213_plane14 ∈ rev213_planes := by decide
def rev213_plane15 : IntegerPlane := ⟨15204000000,(-2139684000000),(-1555517771568)⟩
theorem rev213_plane15_mem : rev213_plane15 ∈ rev213_planes := by decide
def rev213_plane56 : IntegerPlane := ⟨287616000000,1855520000000,1643759759600⟩
theorem rev213_plane56_mem : rev213_plane56 ∈ rev213_planes := by decide
def rev213_plane79 : IntegerPlane := ⟨1440116000000,2129316000000,2741459880216⟩
theorem rev213_plane79_mem : rev213_plane79 ∈ rev213_planes := by decide
def rev213_vertex0 : FractionPoint := fractionRow213[0]!
theorem rev213_vertex0_mem : rev213_vertex0∈fractionRow213 := by decide
def rev213_vertex1 : FractionPoint := fractionRow213[1]!
theorem rev213_vertex1_mem : rev213_vertex1∈fractionRow213 := by decide
def rev213_vertex2 : FractionPoint := fractionRow213[2]!
theorem rev213_vertex2_mem : rev213_vertex2∈fractionRow213 := by decide
def rev213_vertex3 : FractionPoint := fractionRow213[3]!
theorem rev213_vertex3_mem : rev213_vertex3∈fractionRow213 := by decide
def rev213_s0_ll : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev213_s0_ll_mem : rev213_s0_ll.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane14 rev213_vertex0 rev213_vertex1 rev213_s0_ll
    rev213_vertex0_mem rev213_vertex1_mem (by decide)
def rev213_s0_lr : FractionPoint := ⟨4958592752081121,6436683405200000,8859373040646928435359,11586963448453754000000⟩
theorem rev213_s0_lr_mem : rev213_s0_lr.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane14 rev213_vertex0 rev213_vertex1 rev213_s0_lr
    rev213_vertex0_mem rev213_vertex1_mem (by decide)
def rev213_s0_ul : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev213_s0_ul_mem : rev213_s0_ul.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane56 rev213_vertex0 rev213_vertex3 rev213_s0_ul
    rev213_vertex0_mem rev213_vertex3_mem (by decide)
def rev213_s0_ur : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev213_s0_ur_mem : rev213_s0_ur.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane56 rev213_vertex0 rev213_vertex3 rev213_s0_ur
    rev213_vertex0_mem rev213_vertex3_mem (by decide)
theorem rev213_slab0 (p : Point) (hp : p∈IntegerCarrier rev213_planes)
    (hx0 : rev213_s0_ll.real.1≤p.1) (hx1 : p.1≤rev213_s0_lr.real.1) :
    p∈rationalHull (fractionRow213.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev213_plane14 rev213_plane56 rev213_s0_ll rev213_s0_lr rev213_s0_ul rev213_s0_ur
    (by decide) rev213_s0_ll_mem rev213_s0_lr_mem rev213_s0_ul_mem rev213_s0_ur_mem p
    (hp _ rev213_plane14_mem) (hp _ rev213_plane56_mem) hx0 hx1
def rev213_s1_ll : FractionPoint := ⟨4958592752081121,6436683405200000,8859373040646928435359,11586963448453754000000⟩
theorem rev213_s1_ll_mem : rev213_s1_ll.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane14 rev213_vertex0 rev213_vertex1 rev213_s1_ll
    rev213_vertex0_mem rev213_vertex1_mem (by decide)
def rev213_s1_lr : FractionPoint := ⟨1642088682618057,2073350951000000,216994696901067,296192993000000⟩
theorem rev213_s1_lr_mem : rev213_s1_lr.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane14 rev213_vertex0 rev213_vertex1 rev213_s1_lr
    rev213_vertex0_mem rev213_vertex1_mem (by decide)
def rev213_s1_ul : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev213_s1_ul_mem : rev213_s1_ul.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane79 rev213_vertex3 rev213_vertex2 rev213_s1_ul
    rev213_vertex3_mem rev213_vertex2_mem (by decide)
def rev213_s1_ur : FractionPoint := ⟨1642088682618057,2073350951000000,276600855376416992567,367901612798293000000⟩
theorem rev213_s1_ur_mem : rev213_s1_ur.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane79 rev213_vertex3 rev213_vertex2 rev213_s1_ur
    rev213_vertex3_mem rev213_vertex2_mem (by decide)
theorem rev213_slab1 (p : Point) (hp : p∈IntegerCarrier rev213_planes)
    (hx0 : rev213_s1_ll.real.1≤p.1) (hx1 : p.1≤rev213_s1_lr.real.1) :
    p∈rationalHull (fractionRow213.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev213_plane14 rev213_plane79 rev213_s1_ll rev213_s1_lr rev213_s1_ul rev213_s1_ur
    (by decide) rev213_s1_ll_mem rev213_s1_lr_mem rev213_s1_ul_mem rev213_s1_ur_mem p
    (hp _ rev213_plane14_mem) (hp _ rev213_plane79_mem) hx0 hx1
def rev213_s2_ll : FractionPoint := ⟨1642088682618057,2073350951000000,216994696901067,296192993000000⟩
theorem rev213_s2_ll_mem : rev213_s2_ll.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane15 rev213_vertex1 rev213_vertex2 rev213_s2_ll
    rev213_vertex1_mem rev213_vertex2_mem (by decide)
def rev213_s2_lr : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev213_s2_lr_mem : rev213_s2_lr.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane15 rev213_vertex1 rev213_vertex2 rev213_s2_lr
    rev213_vertex1_mem rev213_vertex2_mem (by decide)
def rev213_s2_ul : FractionPoint := ⟨1642088682618057,2073350951000000,276600855376416992567,367901612798293000000⟩
theorem rev213_s2_ul_mem : rev213_s2_ul.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane79 rev213_vertex3 rev213_vertex2 rev213_s2_ul
    rev213_vertex3_mem rev213_vertex2_mem (by decide)
def rev213_s2_ur : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev213_s2_ur_mem : rev213_s2_ur.real ∈ rationalHull (fractionRow213.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow213 rev213_plane79 rev213_vertex3 rev213_vertex2 rev213_s2_ur
    rev213_vertex3_mem rev213_vertex2_mem (by decide)
theorem rev213_slab2 (p : Point) (hp : p∈IntegerCarrier rev213_planes)
    (hx0 : rev213_s2_ll.real.1≤p.1) (hx1 : p.1≤rev213_s2_lr.real.1) :
    p∈rationalHull (fractionRow213.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev213_plane15 rev213_plane79 rev213_s2_ll rev213_s2_lr rev213_s2_ul rev213_s2_ur
    (by decide) rev213_s2_ll_mem rev213_s2_lr_mem rev213_s2_ul_mem rev213_s2_ur_mem p
    (hp _ rev213_plane15_mem) (hp _ rev213_plane79_mem) hx0 hx1
theorem rev213_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev213_planes) : rev213_s0_ll.real.1≤p.1 := by
  have hc := rev213_plane14.combine_sound rev213_plane56 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev213_plane14_mem) (hp _ rev213_plane56_mem)
  exact (rev213_plane14.combine rev213_plane56 1855520000000 1440116000000).xBoundCheck_sound rev213_s0_ll.nx rev213_s0_ll.dx true (by decide) p hc
theorem rev213_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev213_planes) : p.1≤rev213_s2_lr.real.1 := by
  have hc := rev213_plane15.combine_sound rev213_plane79 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev213_plane15_mem) (hp _ rev213_plane79_mem)
  exact (rev213_plane15.combine rev213_plane79 2129316000000 2139684000000).xBoundCheck_sound rev213_s2_lr.nx rev213_s2_lr.dx false (by decide) p hc
theorem rev213_hull (p : Point) (hp : p∈IntegerCarrier rev213_planes) :
    p∈rationalHull (fractionRow213.map FractionPoint.rational) := by
  have hxlo := rev213_bound0_lo p hp
  have hxhi := rev213_bound0_hi p hp
  by_cases h0 : p.1≤rev213_s0_lr.real.1
  · exact rev213_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev213_s1_lr.real.1
  · exact rev213_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev213_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull213 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow213 := by
  rw [← fractionRow213_correct]
  exact rev213_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull213
