import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev9_planes : List IntegerPlane := integerOverlayPlanes ![0,7,3,5]
def rev9_plane9 : IntegerPlane := ⟨2129316000000,1440116000000,827972119784⟩
theorem rev9_plane9_mem : rev9_plane9 ∈ rev9_planes := by decide
def rev9_plane46 : IntegerPlane := ⟨287616000000,1855520000000,499376240400⟩
theorem rev9_plane46_mem : rev9_plane46 ∈ rev9_planes := by decide
def rev9_plane51 : IntegerPlane := ⟨1861776000000,(-202532000000),383371739447⟩
theorem rev9_plane51_mem : rev9_plane51 ∈ rev9_planes := by decide
def rev9_plane64 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-827972119784)⟩
theorem rev9_plane64_mem : rev9_plane64 ∈ rev9_planes := by decide
def rev9_vertex0 : FractionPoint := fractionRow9[0]!
theorem rev9_vertex0_mem : rev9_vertex0∈fractionRow9 := by decide
def rev9_vertex1 : FractionPoint := fractionRow9[1]!
theorem rev9_vertex1_mem : rev9_vertex1∈fractionRow9 := by decide
def rev9_vertex2 : FractionPoint := fractionRow9[2]!
theorem rev9_vertex2_mem : rev9_vertex2∈fractionRow9 := by decide
def rev9_vertex3 : FractionPoint := fractionRow9[3]!
theorem rev9_vertex3_mem : rev9_vertex3∈fractionRow9 := by decide
def rev9_s0_ll : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev9_s0_ll_mem : rev9_s0_ll.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane64 rev9_vertex2 rev9_vertex3 rev9_s0_ll
    rev9_vertex2_mem rev9_vertex3_mem (by decide)
def rev9_s0_lr : FractionPoint := ⟨2553622230880379,11052462565200000,6842023282869278032441,29417731724351754000000⟩
theorem rev9_s0_lr_mem : rev9_s0_lr.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane64 rev9_vertex2 rev9_vertex3 rev9_s0_lr
    rev9_vertex2_mem rev9_vertex3_mem (by decide)
def rev9_s0_ul : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev9_s0_ul_mem : rev9_s0_ul.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane46 rev9_vertex2 rev9_vertex1 rev9_s0_ul
    rev9_vertex2_mem rev9_vertex1_mem (by decide)
def rev9_s0_ur : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev9_s0_ur_mem : rev9_s0_ur.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane46 rev9_vertex2 rev9_vertex1 rev9_s0_ur
    rev9_vertex2_mem rev9_vertex1_mem (by decide)
theorem rev9_slab0 (p : Point) (hp : p∈IntegerCarrier rev9_planes)
    (hx0 : rev9_s0_ll.real.1≤p.1) (hx1 : p.1≤rev9_s0_lr.real.1) :
    p∈rationalHull (fractionRow9.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev9_plane64 rev9_plane46 rev9_s0_ll rev9_s0_lr rev9_s0_ul rev9_s0_ur
    (by decide) rev9_s0_ll_mem rev9_s0_lr_mem rev9_s0_ul_mem rev9_s0_ur_mem p
    (hp _ rev9_plane64_mem) (hp _ rev9_plane46_mem) hx0 hx1
def rev9_s1_ll : FractionPoint := ⟨2553622230880379,11052462565200000,6842023282869278032441,29417731724351754000000⟩
theorem rev9_s1_ll_mem : rev9_s1_ll.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane64 rev9_vertex2 rev9_vertex3 rev9_s1_ll
    rev9_vertex2_mem rev9_vertex3_mem (by decide)
def rev9_s1_lr : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev9_s1_lr_mem : rev9_s1_lr.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane64 rev9_vertex2 rev9_vertex3 rev9_s1_lr
    rev9_vertex2_mem rev9_vertex3_mem (by decide)
def rev9_s1_ul : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev9_s1_ul_mem : rev9_s1_ul.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane9 rev9_vertex1 rev9_vertex0 rev9_s1_ul
    rev9_vertex1_mem rev9_vertex0_mem (by decide)
def rev9_s1_ur : FractionPoint := ⟨49200521405821067,212798949946400000,89285175296466037599257,383068965751262228000000⟩
theorem rev9_s1_ur_mem : rev9_s1_ur.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane9 rev9_vertex1 rev9_vertex0 rev9_s1_ur
    rev9_vertex1_mem rev9_vertex0_mem (by decide)
theorem rev9_slab1 (p : Point) (hp : p∈IntegerCarrier rev9_planes)
    (hx0 : rev9_s1_ll.real.1≤p.1) (hx1 : p.1≤rev9_s1_lr.real.1) :
    p∈rationalHull (fractionRow9.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev9_plane64 rev9_plane9 rev9_s1_ll rev9_s1_lr rev9_s1_ul rev9_s1_ur
    (by decide) rev9_s1_ll_mem rev9_s1_lr_mem rev9_s1_ul_mem rev9_s1_ur_mem p
    (hp _ rev9_plane64_mem) (hp _ rev9_plane9_mem) hx0 hx1
def rev9_s2_ll : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev9_s2_ll_mem : rev9_s2_ll.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane51 rev9_vertex3 rev9_vertex0 rev9_s2_ll
    rev9_vertex3_mem rev9_vertex0_mem (by decide)
def rev9_s2_lr : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev9_s2_lr_mem : rev9_s2_lr.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane51 rev9_vertex3 rev9_vertex0 rev9_s2_lr
    rev9_vertex3_mem rev9_vertex0_mem (by decide)
def rev9_s2_ul : FractionPoint := ⟨49200521405821067,212798949946400000,89285175296466037599257,383068965751262228000000⟩
theorem rev9_s2_ul_mem : rev9_s2_ul.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane9 rev9_vertex1 rev9_vertex0 rev9_s2_ul
    rev9_vertex1_mem rev9_vertex0_mem (by decide)
def rev9_s2_ur : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev9_s2_ur_mem : rev9_s2_ur.real ∈ rationalHull (fractionRow9.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow9 rev9_plane9 rev9_vertex1 rev9_vertex0 rev9_s2_ur
    rev9_vertex1_mem rev9_vertex0_mem (by decide)
theorem rev9_slab2 (p : Point) (hp : p∈IntegerCarrier rev9_planes)
    (hx0 : rev9_s2_ll.real.1≤p.1) (hx1 : p.1≤rev9_s2_lr.real.1) :
    p∈rationalHull (fractionRow9.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev9_plane51 rev9_plane9 rev9_s2_ll rev9_s2_lr rev9_s2_ul rev9_s2_ur
    (by decide) rev9_s2_ll_mem rev9_s2_lr_mem rev9_s2_ul_mem rev9_s2_ur_mem p
    (hp _ rev9_plane51_mem) (hp _ rev9_plane9_mem) hx0 hx1
theorem rev9_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev9_planes) : rev9_s0_ll.real.1≤p.1 := by
  have hc := rev9_plane46.combine_sound rev9_plane64 2129316000000 1855520000000 (by decide) (by decide) p
    (hp _ rev9_plane46_mem) (hp _ rev9_plane64_mem)
  exact (rev9_plane46.combine rev9_plane64 2129316000000 1855520000000).xBoundCheck_sound rev9_s0_ll.nx rev9_s0_ll.dx true (by decide) p hc
theorem rev9_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev9_planes) : p.1≤rev9_s2_lr.real.1 := by
  have hc := rev9_plane9.combine_sound rev9_plane51 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev9_plane9_mem) (hp _ rev9_plane51_mem)
  exact (rev9_plane9.combine rev9_plane51 202532000000 1440116000000).xBoundCheck_sound rev9_s2_lr.nx rev9_s2_lr.dx false (by decide) p hc
theorem rev9_hull (p : Point) (hp : p∈IntegerCarrier rev9_planes) :
    p∈rationalHull (fractionRow9.map FractionPoint.rational) := by
  have hxlo := rev9_bound0_lo p hp
  have hxhi := rev9_bound0_hi p hp
  by_cases h0 : p.1≤rev9_s0_lr.real.1
  · exact rev9_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev9_s1_lr.real.1
  · exact rev9_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev9_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull9 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,3,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow9 := by
  rw [← fractionRow9_correct]
  exact rev9_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull9
