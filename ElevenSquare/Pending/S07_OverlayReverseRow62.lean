import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev62_planes : List IntegerPlane := integerOverlayPlanes ![5,3,7,0]
def rev62_plane4 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-827972119784)⟩
theorem rev62_plane4_mem : rev62_plane4 ∈ rev62_planes := by decide
def rev62_plane26 : IntegerPlane := ⟨1855520000000,287616000000,499376240400⟩
theorem rev62_plane26_mem : rev62_plane26 ∈ rev62_planes := by decide
def rev62_plane31 : IntegerPlane := ⟨(-202532000000),1861776000000,383371739447⟩
theorem rev62_plane31_mem : rev62_plane31 ∈ rev62_planes := by decide
def rev62_plane69 : IntegerPlane := ⟨1440116000000,2129316000000,827972119784⟩
theorem rev62_plane69_mem : rev62_plane69 ∈ rev62_planes := by decide
def rev62_vertex0 : FractionPoint := fractionRow62[0]!
theorem rev62_vertex0_mem : rev62_vertex0∈fractionRow62 := by decide
def rev62_vertex1 : FractionPoint := fractionRow62[1]!
theorem rev62_vertex1_mem : rev62_vertex1∈fractionRow62 := by decide
def rev62_vertex2 : FractionPoint := fractionRow62[2]!
theorem rev62_vertex2_mem : rev62_vertex2∈fractionRow62 := by decide
def rev62_vertex3 : FractionPoint := fractionRow62[3]!
theorem rev62_vertex3_mem : rev62_vertex3∈fractionRow62 := by decide
def rev62_s0_ll : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev62_s0_ll_mem : rev62_s0_ll.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane4 rev62_vertex0 rev62_vertex1 rev62_s0_ll
    rev62_vertex0_mem rev62_vertex1_mem (by decide)
def rev62_s0_lr : FractionPoint := ⟨8633083839650573,37052714692000000,87828936986982865489,381144337652744800000⟩
theorem rev62_s0_lr_mem : rev62_s0_lr.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane4 rev62_vertex0 rev62_vertex1 rev62_s0_lr
    rev62_vertex0_mem rev62_vertex1_mem (by decide)
def rev62_s0_ul : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev62_s0_ul_mem : rev62_s0_ul.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane31 rev62_vertex0 rev62_vertex3 rev62_s0_ul
    rev62_vertex0_mem rev62_vertex3_mem (by decide)
def rev62_s0_ur : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev62_s0_ur_mem : rev62_s0_ur.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane31 rev62_vertex0 rev62_vertex3 rev62_s0_ur
    rev62_vertex0_mem rev62_vertex3_mem (by decide)
theorem rev62_slab0 (p : Point) (hp : p∈IntegerCarrier rev62_planes)
    (hx0 : rev62_s0_ll.real.1≤p.1) (hx1 : p.1≤rev62_s0_lr.real.1) :
    p∈rationalHull (fractionRow62.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev62_plane4 rev62_plane31 rev62_s0_ll rev62_s0_lr rev62_s0_ul rev62_s0_ur
    (by decide) rev62_s0_ll_mem rev62_s0_lr_mem rev62_s0_ul_mem rev62_s0_ur_mem p
    (hp _ rev62_plane4_mem) (hp _ rev62_plane31_mem) hx0 hx1
def rev62_s1_ll : FractionPoint := ⟨8633083839650573,37052714692000000,87828936986982865489,381144337652744800000⟩
theorem rev62_s1_ll_mem : rev62_s1_ll.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane4 rev62_vertex0 rev62_vertex1 rev62_s1_ll
    rev62_vertex0_mem rev62_vertex1_mem (by decide)
def rev62_s1_lr : FractionPoint := ⟨613981986234949,2631538706000000,43573950684930384731,189486049756494800000⟩
theorem rev62_s1_lr_mem : rev62_s1_lr.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane4 rev62_vertex0 rev62_vertex1 rev62_s1_lr
    rev62_vertex0_mem rev62_vertex1_mem (by decide)
def rev62_s1_ul : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev62_s1_ul_mem : rev62_s1_ul.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane69 rev62_vertex3 rev62_vertex2 rev62_s1_ul
    rev62_vertex3_mem rev62_vertex2_mem (by decide)
def rev62_s1_ur : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev62_s1_ur_mem : rev62_s1_ur.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane69 rev62_vertex3 rev62_vertex2 rev62_s1_ur
    rev62_vertex3_mem rev62_vertex2_mem (by decide)
theorem rev62_slab1 (p : Point) (hp : p∈IntegerCarrier rev62_planes)
    (hx0 : rev62_s1_ll.real.1≤p.1) (hx1 : p.1≤rev62_s1_lr.real.1) :
    p∈rationalHull (fractionRow62.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev62_plane4 rev62_plane69 rev62_s1_ll rev62_s1_lr rev62_s1_ul rev62_s1_ur
    (by decide) rev62_s1_ll_mem rev62_s1_lr_mem rev62_s1_ul_mem rev62_s1_ur_mem p
    (hp _ rev62_plane4_mem) (hp _ rev62_plane69_mem) hx0 hx1
def rev62_s2_ll : FractionPoint := ⟨613981986234949,2631538706000000,43573950684930384731,189486049756494800000⟩
theorem rev62_s2_ll_mem : rev62_s2_ll.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane4 rev62_vertex0 rev62_vertex1 rev62_s2_ll
    rev62_vertex0_mem rev62_vertex1_mem (by decide)
def rev62_s2_lr : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev62_s2_lr_mem : rev62_s2_lr.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane4 rev62_vertex0 rev62_vertex1 rev62_s2_lr
    rev62_vertex0_mem rev62_vertex1_mem (by decide)
def rev62_s2_ul : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev62_s2_ul_mem : rev62_s2_ul.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane26 rev62_vertex2 rev62_vertex1 rev62_s2_ul
    rev62_vertex2_mem rev62_vertex1_mem (by decide)
def rev62_s2_ur : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev62_s2_ur_mem : rev62_s2_ur.real ∈ rationalHull (fractionRow62.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow62 rev62_plane26 rev62_vertex2 rev62_vertex1 rev62_s2_ur
    rev62_vertex2_mem rev62_vertex1_mem (by decide)
theorem rev62_slab2 (p : Point) (hp : p∈IntegerCarrier rev62_planes)
    (hx0 : rev62_s2_ll.real.1≤p.1) (hx1 : p.1≤rev62_s2_lr.real.1) :
    p∈rationalHull (fractionRow62.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev62_plane4 rev62_plane26 rev62_s2_ll rev62_s2_lr rev62_s2_ul rev62_s2_ur
    (by decide) rev62_s2_ll_mem rev62_s2_lr_mem rev62_s2_ul_mem rev62_s2_ur_mem p
    (hp _ rev62_plane4_mem) (hp _ rev62_plane26_mem) hx0 hx1
theorem rev62_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev62_planes) : rev62_s0_ll.real.1≤p.1 := by
  have hc := rev62_plane4.combine_sound rev62_plane31 1861776000000 1440116000000 (by decide) (by decide) p
    (hp _ rev62_plane4_mem) (hp _ rev62_plane31_mem)
  exact (rev62_plane4.combine rev62_plane31 1861776000000 1440116000000).xBoundCheck_sound rev62_s0_ll.nx rev62_s0_ll.dx true (by decide) p hc
theorem rev62_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev62_planes) : p.1≤rev62_s2_lr.real.1 := by
  have hc := rev62_plane4.combine_sound rev62_plane26 287616000000 1440116000000 (by decide) (by decide) p
    (hp _ rev62_plane4_mem) (hp _ rev62_plane26_mem)
  exact (rev62_plane4.combine rev62_plane26 287616000000 1440116000000).xBoundCheck_sound rev62_s2_lr.nx rev62_s2_lr.dx false (by decide) p hc
theorem rev62_hull (p : Point) (hp : p∈IntegerCarrier rev62_planes) :
    p∈rationalHull (fractionRow62.map FractionPoint.rational) := by
  have hxlo := rev62_bound0_lo p hp
  have hxhi := rev62_bound0_hi p hp
  by_cases h0 : p.1≤rev62_s0_lr.real.1
  · exact rev62_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev62_s1_lr.real.1
  · exact rev62_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev62_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull62 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,3,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow62 := by
  rw [← fractionRow62_correct]
  exact rev62_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull62
