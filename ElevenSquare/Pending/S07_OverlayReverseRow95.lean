import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev95_planes : List IntegerPlane := integerOverlayPlanes ![7,0,10,13]
def rev95_plane28 : IntegerPlane := ⟨15204000000,2139684000000,584166228432⟩
theorem rev95_plane28_mem : rev95_plane28 ∈ rev95_planes := by decide
def rev95_plane29 : IntegerPlane := ⟨(-2129316000000),1440116000000,(-1301343880216)⟩
theorem rev95_plane29_mem : rev95_plane29 ∈ rev95_planes := by decide
def rev95_plane59 : IntegerPlane := ⟨1440116000000,(-2129316000000),612143880216⟩
theorem rev95_plane59_mem : rev95_plane59 ∈ rev95_planes := by decide
def rev95_plane76 : IntegerPlane := ⟨287616000000,(-1855520000000),(-211760240400)⟩
theorem rev95_plane76_mem : rev95_plane76 ∈ rev95_planes := by decide
def rev95_vertex0 : FractionPoint := fractionRow95[0]!
theorem rev95_vertex0_mem : rev95_vertex0∈fractionRow95 := by decide
def rev95_vertex1 : FractionPoint := fractionRow95[1]!
theorem rev95_vertex1_mem : rev95_vertex1∈fractionRow95 := by decide
def rev95_vertex2 : FractionPoint := fractionRow95[2]!
theorem rev95_vertex2_mem : rev95_vertex2∈fractionRow95 := by decide
def rev95_vertex3 : FractionPoint := fractionRow95[3]!
theorem rev95_vertex3_mem : rev95_vertex3∈fractionRow95 := by decide
def rev95_s0_ll : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev95_s0_ll_mem : rev95_s0_ll.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane76 rev95_vertex2 rev95_vertex3 rev95_s0_ll
    rev95_vertex2_mem rev95_vertex3_mem (by decide)
def rev95_s0_lr : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev95_s0_lr_mem : rev95_s0_lr.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane76 rev95_vertex2 rev95_vertex3 rev95_s0_lr
    rev95_vertex2_mem rev95_vertex3_mem (by decide)
def rev95_s0_ul : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev95_s0_ul_mem : rev95_s0_ul.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane29 rev95_vertex2 rev95_vertex1 rev95_s0_ul
    rev95_vertex2_mem rev95_vertex1_mem (by decide)
def rev95_s0_ur : FractionPoint := ⟨4958592752081121,6436683405200000,2727590407806825564641,11586963448453754000000⟩
theorem rev95_s0_ur_mem : rev95_s0_ur.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane29 rev95_vertex2 rev95_vertex1 rev95_s0_ur
    rev95_vertex2_mem rev95_vertex1_mem (by decide)
theorem rev95_slab0 (p : Point) (hp : p∈IntegerCarrier rev95_planes)
    (hx0 : rev95_s0_ll.real.1≤p.1) (hx1 : p.1≤rev95_s0_lr.real.1) :
    p∈rationalHull (fractionRow95.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev95_plane76 rev95_plane29 rev95_s0_ll rev95_s0_lr rev95_s0_ul rev95_s0_ur
    (by decide) rev95_s0_ll_mem rev95_s0_lr_mem rev95_s0_ul_mem rev95_s0_ur_mem p
    (hp _ rev95_plane76_mem) (hp _ rev95_plane29_mem) hx0 hx1
def rev95_s1_ll : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev95_s1_ll_mem : rev95_s1_ll.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane59 rev95_vertex3 rev95_vertex0 rev95_s1_ll
    rev95_vertex3_mem rev95_vertex0_mem (by decide)
def rev95_s1_lr : FractionPoint := ⟨1642088682618057,2073350951000000,91300757421876007433,367901612798293000000⟩
theorem rev95_s1_lr_mem : rev95_s1_lr.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane59 rev95_vertex3 rev95_vertex0 rev95_s1_lr
    rev95_vertex3_mem rev95_vertex0_mem (by decide)
def rev95_s1_ul : FractionPoint := ⟨4958592752081121,6436683405200000,2727590407806825564641,11586963448453754000000⟩
theorem rev95_s1_ul_mem : rev95_s1_ul.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane29 rev95_vertex2 rev95_vertex1 rev95_s1_ul
    rev95_vertex2_mem rev95_vertex1_mem (by decide)
def rev95_s1_ur : FractionPoint := ⟨1642088682618057,2073350951000000,79198296098933,296192993000000⟩
theorem rev95_s1_ur_mem : rev95_s1_ur.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane29 rev95_vertex2 rev95_vertex1 rev95_s1_ur
    rev95_vertex2_mem rev95_vertex1_mem (by decide)
theorem rev95_slab1 (p : Point) (hp : p∈IntegerCarrier rev95_planes)
    (hx0 : rev95_s1_ll.real.1≤p.1) (hx1 : p.1≤rev95_s1_lr.real.1) :
    p∈rationalHull (fractionRow95.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev95_plane59 rev95_plane29 rev95_s1_ll rev95_s1_lr rev95_s1_ul rev95_s1_ur
    (by decide) rev95_s1_ll_mem rev95_s1_lr_mem rev95_s1_ul_mem rev95_s1_ur_mem p
    (hp _ rev95_plane59_mem) (hp _ rev95_plane29_mem) hx0 hx1
def rev95_s2_ll : FractionPoint := ⟨1642088682618057,2073350951000000,91300757421876007433,367901612798293000000⟩
theorem rev95_s2_ll_mem : rev95_s2_ll.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane59 rev95_vertex3 rev95_vertex0 rev95_s2_ll
    rev95_vertex3_mem rev95_vertex0_mem (by decide)
def rev95_s2_lr : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev95_s2_lr_mem : rev95_s2_lr.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane59 rev95_vertex3 rev95_vertex0 rev95_s2_lr
    rev95_vertex3_mem rev95_vertex0_mem (by decide)
def rev95_s2_ul : FractionPoint := ⟨1642088682618057,2073350951000000,79198296098933,296192993000000⟩
theorem rev95_s2_ul_mem : rev95_s2_ul.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane28 rev95_vertex1 rev95_vertex0 rev95_s2_ul
    rev95_vertex1_mem rev95_vertex0_mem (by decide)
def rev95_s2_ur : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev95_s2_ur_mem : rev95_s2_ur.real ∈ rationalHull (fractionRow95.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow95 rev95_plane28 rev95_vertex1 rev95_vertex0 rev95_s2_ur
    rev95_vertex1_mem rev95_vertex0_mem (by decide)
theorem rev95_slab2 (p : Point) (hp : p∈IntegerCarrier rev95_planes)
    (hx0 : rev95_s2_ll.real.1≤p.1) (hx1 : p.1≤rev95_s2_lr.real.1) :
    p∈rationalHull (fractionRow95.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev95_plane59 rev95_plane28 rev95_s2_ll rev95_s2_lr rev95_s2_ul rev95_s2_ur
    (by decide) rev95_s2_ll_mem rev95_s2_lr_mem rev95_s2_ul_mem rev95_s2_ur_mem p
    (hp _ rev95_plane59_mem) (hp _ rev95_plane28_mem) hx0 hx1
theorem rev95_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev95_planes) : rev95_s0_ll.real.1≤p.1 := by
  have hc := rev95_plane29.combine_sound rev95_plane76 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev95_plane29_mem) (hp _ rev95_plane76_mem)
  exact (rev95_plane29.combine rev95_plane76 1855520000000 1440116000000).xBoundCheck_sound rev95_s0_ll.nx rev95_s0_ll.dx true (by decide) p hc
theorem rev95_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev95_planes) : p.1≤rev95_s2_lr.real.1 := by
  have hc := rev95_plane28.combine_sound rev95_plane59 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev95_plane28_mem) (hp _ rev95_plane59_mem)
  exact (rev95_plane28.combine rev95_plane59 2129316000000 2139684000000).xBoundCheck_sound rev95_s2_lr.nx rev95_s2_lr.dx false (by decide) p hc
theorem rev95_hull (p : Point) (hp : p∈IntegerCarrier rev95_planes) :
    p∈rationalHull (fractionRow95.map FractionPoint.rational) := by
  have hxlo := rev95_bound0_lo p hp
  have hxhi := rev95_bound0_hi p hp
  by_cases h0 : p.1≤rev95_s0_lr.real.1
  · exact rev95_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev95_s1_lr.real.1
  · exact rev95_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev95_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull95 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow95 := by
  rw [← fractionRow95_correct]
  exact rev95_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull95
