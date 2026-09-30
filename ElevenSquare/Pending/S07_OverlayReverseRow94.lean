import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev94_planes : List IntegerPlane := integerOverlayPlanes ![7,0,10,12]
def rev94_plane29 : IntegerPlane := ⟨(-2129316000000),1440116000000,(-1301343880216)⟩
theorem rev94_plane29_mem : rev94_plane29 ∈ rev94_planes := by decide
def rev94_plane59 : IntegerPlane := ⟨1440116000000,(-2129316000000),612143880216⟩
theorem rev94_plane59_mem : rev94_plane59 ∈ rev94_planes := by decide
def rev94_plane72 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-1478404260553)⟩
theorem rev94_plane72_mem : rev94_plane72 ∈ rev94_planes := by decide
def rev94_plane77 : IntegerPlane := ⟨(-287616000000),1855520000000,211760240400⟩
theorem rev94_plane77_mem : rev94_plane77 ∈ rev94_planes := by decide
def rev94_vertex0 : FractionPoint := fractionRow94[0]!
theorem rev94_vertex0_mem : rev94_vertex0∈fractionRow94 := by decide
def rev94_vertex1 : FractionPoint := fractionRow94[1]!
theorem rev94_vertex1_mem : rev94_vertex1∈fractionRow94 := by decide
def rev94_vertex2 : FractionPoint := fractionRow94[2]!
theorem rev94_vertex2_mem : rev94_vertex2∈fractionRow94 := by decide
def rev94_vertex3 : FractionPoint := fractionRow94[3]!
theorem rev94_vertex3_mem : rev94_vertex3∈fractionRow94 := by decide
def rev94_s0_ll : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev94_s0_ll_mem : rev94_s0_ll.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane72 rev94_vertex1 rev94_vertex2 rev94_s0_ll
    rev94_vertex1_mem rev94_vertex2_mem (by decide)
def rev94_s0_lr : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev94_s0_lr_mem : rev94_s0_lr.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane72 rev94_vertex1 rev94_vertex2 rev94_s0_lr
    rev94_vertex1_mem rev94_vertex2_mem (by decide)
def rev94_s0_ul : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev94_s0_ul_mem : rev94_s0_ul.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane29 rev94_vertex1 rev94_vertex0 rev94_s0_ul
    rev94_vertex1_mem rev94_vertex0_mem (by decide)
def rev94_s0_ur : FractionPoint := ⟨163598428540578933,212798949946400000,89285175296466037599257,383068965751262228000000⟩
theorem rev94_s0_ur_mem : rev94_s0_ur.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane29 rev94_vertex1 rev94_vertex0 rev94_s0_ur
    rev94_vertex1_mem rev94_vertex0_mem (by decide)
theorem rev94_slab0 (p : Point) (hp : p∈IntegerCarrier rev94_planes)
    (hx0 : rev94_s0_ll.real.1≤p.1) (hx1 : p.1≤rev94_s0_lr.real.1) :
    p∈rationalHull (fractionRow94.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev94_plane72 rev94_plane29 rev94_s0_ll rev94_s0_lr rev94_s0_ul rev94_s0_ur
    (by decide) rev94_s0_ll_mem rev94_s0_lr_mem rev94_s0_ul_mem rev94_s0_ur_mem p
    (hp _ rev94_plane72_mem) (hp _ rev94_plane29_mem) hx0 hx1
def rev94_s1_ll : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev94_s1_ll_mem : rev94_s1_ll.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane59 rev94_vertex2 rev94_vertex3 rev94_s1_ll
    rev94_vertex2_mem rev94_vertex3_mem (by decide)
def rev94_s1_lr : FractionPoint := ⟨8498840334319621,11052462565200000,6842023282869278032441,29417731724351754000000⟩
theorem rev94_s1_lr_mem : rev94_s1_lr.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane59 rev94_vertex2 rev94_vertex3 rev94_s1_lr
    rev94_vertex2_mem rev94_vertex3_mem (by decide)
def rev94_s1_ul : FractionPoint := ⟨163598428540578933,212798949946400000,89285175296466037599257,383068965751262228000000⟩
theorem rev94_s1_ul_mem : rev94_s1_ul.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane29 rev94_vertex1 rev94_vertex0 rev94_s1_ul
    rev94_vertex1_mem rev94_vertex0_mem (by decide)
def rev94_s1_ur : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev94_s1_ur_mem : rev94_s1_ur.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane29 rev94_vertex1 rev94_vertex0 rev94_s1_ur
    rev94_vertex1_mem rev94_vertex0_mem (by decide)
theorem rev94_slab1 (p : Point) (hp : p∈IntegerCarrier rev94_planes)
    (hx0 : rev94_s1_ll.real.1≤p.1) (hx1 : p.1≤rev94_s1_lr.real.1) :
    p∈rationalHull (fractionRow94.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev94_plane59 rev94_plane29 rev94_s1_ll rev94_s1_lr rev94_s1_ul rev94_s1_ur
    (by decide) rev94_s1_ll_mem rev94_s1_lr_mem rev94_s1_ul_mem rev94_s1_ur_mem p
    (hp _ rev94_plane59_mem) (hp _ rev94_plane29_mem) hx0 hx1
def rev94_s2_ll : FractionPoint := ⟨8498840334319621,11052462565200000,6842023282869278032441,29417731724351754000000⟩
theorem rev94_s2_ll_mem : rev94_s2_ll.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane59 rev94_vertex2 rev94_vertex3 rev94_s2_ll
    rev94_vertex2_mem rev94_vertex3_mem (by decide)
def rev94_s2_lr : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev94_s2_lr_mem : rev94_s2_lr.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane59 rev94_vertex2 rev94_vertex3 rev94_s2_lr
    rev94_vertex2_mem rev94_vertex3_mem (by decide)
def rev94_s2_ul : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev94_s2_ul_mem : rev94_s2_ul.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane77 rev94_vertex0 rev94_vertex3 rev94_s2_ul
    rev94_vertex0_mem rev94_vertex3_mem (by decide)
def rev94_s2_ur : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev94_s2_ur_mem : rev94_s2_ur.real ∈ rationalHull (fractionRow94.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow94 rev94_plane77 rev94_vertex0 rev94_vertex3 rev94_s2_ur
    rev94_vertex0_mem rev94_vertex3_mem (by decide)
theorem rev94_slab2 (p : Point) (hp : p∈IntegerCarrier rev94_planes)
    (hx0 : rev94_s2_ll.real.1≤p.1) (hx1 : p.1≤rev94_s2_lr.real.1) :
    p∈rationalHull (fractionRow94.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev94_plane59 rev94_plane77 rev94_s2_ll rev94_s2_lr rev94_s2_ul rev94_s2_ur
    (by decide) rev94_s2_ll_mem rev94_s2_lr_mem rev94_s2_ul_mem rev94_s2_ur_mem p
    (hp _ rev94_plane59_mem) (hp _ rev94_plane77_mem) hx0 hx1
theorem rev94_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev94_planes) : rev94_s0_ll.real.1≤p.1 := by
  have hc := rev94_plane29.combine_sound rev94_plane72 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev94_plane29_mem) (hp _ rev94_plane72_mem)
  exact (rev94_plane29.combine rev94_plane72 202532000000 1440116000000).xBoundCheck_sound rev94_s0_ll.nx rev94_s0_ll.dx true (by decide) p hc
theorem rev94_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev94_planes) : p.1≤rev94_s2_lr.real.1 := by
  have hc := rev94_plane59.combine_sound rev94_plane77 1855520000000 2129316000000 (by decide) (by decide) p
    (hp _ rev94_plane59_mem) (hp _ rev94_plane77_mem)
  exact (rev94_plane59.combine rev94_plane77 1855520000000 2129316000000).xBoundCheck_sound rev94_s2_lr.nx rev94_s2_lr.dx false (by decide) p hc
theorem rev94_hull (p : Point) (hp : p∈IntegerCarrier rev94_planes) :
    p∈rationalHull (fractionRow94.map FractionPoint.rational) := by
  have hxlo := rev94_bound0_lo p hp
  have hxhi := rev94_bound0_hi p hp
  by_cases h0 : p.1≤rev94_s0_lr.real.1
  · exact rev94_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev94_s1_lr.real.1
  · exact rev94_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev94_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull94 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,10,12] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow94 := by
  rw [← fractionRow94_correct]
  exact rev94_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull94
