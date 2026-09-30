import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev7_planes : List IntegerPlane := integerOverlayPlanes ![0,7,3,0]
def rev7_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev7_plane0_mem : rev7_plane0 ∈ rev7_planes := by decide
def rev7_plane27 : IntegerPlane := ⟨202532000000,(-1861776000000),(-383371739447)⟩
theorem rev7_plane27_mem : rev7_plane27 ∈ rev7_planes := by decide
def rev7_plane46 : IntegerPlane := ⟨287616000000,1855520000000,499376240400⟩
theorem rev7_plane46_mem : rev7_plane46 ∈ rev7_planes := by decide
def rev7_plane51 : IntegerPlane := ⟨1861776000000,(-202532000000),383371739447⟩
theorem rev7_plane51_mem : rev7_plane51 ∈ rev7_planes := by decide
def rev7_plane65 : IntegerPlane := ⟨(-699324000000),2145688000000,450639272359⟩
theorem rev7_plane65_mem : rev7_plane65 ∈ rev7_planes := by decide
def rev7_plane69 : IntegerPlane := ⟨1440116000000,2129316000000,827972119784⟩
theorem rev7_plane69_mem : rev7_plane69 ∈ rev7_planes := by decide
def rev7_vertex0 : FractionPoint := fractionRow7[0]!
theorem rev7_vertex0_mem : rev7_vertex0∈fractionRow7 := by decide
def rev7_vertex1 : FractionPoint := fractionRow7[1]!
theorem rev7_vertex1_mem : rev7_vertex1∈fractionRow7 := by decide
def rev7_vertex2 : FractionPoint := fractionRow7[2]!
theorem rev7_vertex2_mem : rev7_vertex2∈fractionRow7 := by decide
def rev7_vertex3 : FractionPoint := fractionRow7[3]!
theorem rev7_vertex3_mem : rev7_vertex3∈fractionRow7 := by decide
def rev7_vertex4 : FractionPoint := fractionRow7[4]!
theorem rev7_vertex4_mem : rev7_vertex4∈fractionRow7 := by decide
def rev7_vertex5 : FractionPoint := fractionRow7[5]!
theorem rev7_vertex5_mem : rev7_vertex5∈fractionRow7 := by decide
def rev7_s0_ll : FractionPoint := ⟨0,1,383371739447,1861776000000⟩
theorem rev7_s0_ll_mem : rev7_s0_ll.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane27 rev7_vertex3 rev7_vertex4 rev7_s0_ll
    rev7_vertex3_mem rev7_vertex4_mem (by decide)
def rev7_s0_lr : FractionPoint := ⟨1470846399148897,11967149176800000,3053600161902484090271,13925094453616248000000⟩
theorem rev7_s0_lr_mem : rev7_s0_lr.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane27 rev7_vertex3 rev7_vertex4 rev7_s0_lr
    rev7_vertex3_mem rev7_vertex4_mem (by decide)
def rev7_s0_ul : FractionPoint := ⟨0,1,450639272359,2145688000000⟩
theorem rev7_s0_ul_mem : rev7_s0_ul.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane65 rev7_vertex2 rev7_vertex1 rev7_s0_ul
    rev7_vertex2_mem rev7_vertex1_mem (by decide)
def rev7_s0_ur : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev7_s0_ur_mem : rev7_s0_ur.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane65 rev7_vertex2 rev7_vertex1 rev7_s0_ur
    rev7_vertex2_mem rev7_vertex1_mem (by decide)
theorem rev7_slab0 (p : Point) (hp : p∈IntegerCarrier rev7_planes)
    (hx0 : rev7_s0_ll.real.1≤p.1) (hx1 : p.1≤rev7_s0_lr.real.1) :
    p∈rationalHull (fractionRow7.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev7_plane27 rev7_plane65 rev7_s0_ll rev7_s0_lr rev7_s0_ul rev7_s0_ur
    (by decide) rev7_s0_ll_mem rev7_s0_lr_mem rev7_s0_ul_mem rev7_s0_ur_mem p
    (hp _ rev7_plane27_mem) (hp _ rev7_plane65_mem) hx0 hx1
def rev7_s1_ll : FractionPoint := ⟨1470846399148897,11967149176800000,3053600161902484090271,13925094453616248000000⟩
theorem rev7_s1_ll_mem : rev7_s1_ll.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane27 rev7_vertex3 rev7_vertex4 rev7_s1_ll
    rev7_vertex3_mem rev7_vertex4_mem (by decide)
def rev7_s1_lr : FractionPoint := ⟨1478090653118879,6436683405200000,6917507923696589816381,29959156708499088000000⟩
theorem rev7_s1_lr_mem : rev7_s1_lr.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane27 rev7_vertex3 rev7_vertex4 rev7_s1_lr
    rev7_vertex3_mem rev7_vertex4_mem (by decide)
def rev7_s1_ul : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev7_s1_ul_mem : rev7_s1_ul.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane46 rev7_vertex1 rev7_vertex0 rev7_s1_ul
    rev7_vertex1_mem rev7_vertex0_mem (by decide)
def rev7_s1_ur : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev7_s1_ur_mem : rev7_s1_ur.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane46 rev7_vertex1 rev7_vertex0 rev7_s1_ur
    rev7_vertex1_mem rev7_vertex0_mem (by decide)
theorem rev7_slab1 (p : Point) (hp : p∈IntegerCarrier rev7_planes)
    (hx0 : rev7_s1_ll.real.1≤p.1) (hx1 : p.1≤rev7_s1_lr.real.1) :
    p∈rationalHull (fractionRow7.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev7_plane27 rev7_plane46 rev7_s1_ll rev7_s1_lr rev7_s1_ul rev7_s1_ur
    (by decide) rev7_s1_ll_mem rev7_s1_lr_mem rev7_s1_ul_mem rev7_s1_ur_mem p
    (hp _ rev7_plane27_mem) (hp _ rev7_plane46_mem) hx0 hx1
def rev7_s2_ll : FractionPoint := ⟨1478090653118879,6436683405200000,6917507923696589816381,29959156708499088000000⟩
theorem rev7_s2_ll_mem : rev7_s2_ll.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane27 rev7_vertex3 rev7_vertex4 rev7_s2_ll
    rev7_vertex3_mem rev7_vertex4_mem (by decide)
def rev7_s2_lr : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev7_s2_lr_mem : rev7_s2_lr.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane27 rev7_vertex3 rev7_vertex4 rev7_s2_lr
    rev7_vertex3_mem rev7_vertex4_mem (by decide)
def rev7_s2_ul : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev7_s2_ul_mem : rev7_s2_ul.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane69 rev7_vertex0 rev7_vertex5 rev7_s2_ul
    rev7_vertex0_mem rev7_vertex5_mem (by decide)
def rev7_s2_ur : FractionPoint := ⟨383371739447,1659244000000,205426998998356861,883263699276000000⟩
theorem rev7_s2_ur_mem : rev7_s2_ur.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane69 rev7_vertex0 rev7_vertex5 rev7_s2_ur
    rev7_vertex0_mem rev7_vertex5_mem (by decide)
theorem rev7_slab2 (p : Point) (hp : p∈IntegerCarrier rev7_planes)
    (hx0 : rev7_s2_ll.real.1≤p.1) (hx1 : p.1≤rev7_s2_lr.real.1) :
    p∈rationalHull (fractionRow7.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev7_plane27 rev7_plane69 rev7_s2_ll rev7_s2_lr rev7_s2_ul rev7_s2_ur
    (by decide) rev7_s2_ll_mem rev7_s2_lr_mem rev7_s2_ul_mem rev7_s2_ur_mem p
    (hp _ rev7_plane27_mem) (hp _ rev7_plane69_mem) hx0 hx1
def rev7_s3_ll : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev7_s3_ll_mem : rev7_s3_ll.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane51 rev7_vertex4 rev7_vertex5 rev7_s3_ll
    rev7_vertex4_mem rev7_vertex5_mem (by decide)
def rev7_s3_lr : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev7_s3_lr_mem : rev7_s3_lr.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane51 rev7_vertex4 rev7_vertex5 rev7_s3_lr
    rev7_vertex4_mem rev7_vertex5_mem (by decide)
def rev7_s3_ul : FractionPoint := ⟨383371739447,1659244000000,205426998998356861,883263699276000000⟩
theorem rev7_s3_ul_mem : rev7_s3_ul.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane69 rev7_vertex0 rev7_vertex5 rev7_s3_ul
    rev7_vertex0_mem rev7_vertex5_mem (by decide)
def rev7_s3_ur : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev7_s3_ur_mem : rev7_s3_ur.real ∈ rationalHull (fractionRow7.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow7 rev7_plane69 rev7_vertex0 rev7_vertex5 rev7_s3_ur
    rev7_vertex0_mem rev7_vertex5_mem (by decide)
theorem rev7_slab3 (p : Point) (hp : p∈IntegerCarrier rev7_planes)
    (hx0 : rev7_s3_ll.real.1≤p.1) (hx1 : p.1≤rev7_s3_lr.real.1) :
    p∈rationalHull (fractionRow7.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev7_plane51 rev7_plane69 rev7_s3_ll rev7_s3_lr rev7_s3_ul rev7_s3_ur
    (by decide) rev7_s3_ll_mem rev7_s3_lr_mem rev7_s3_ul_mem rev7_s3_ur_mem p
    (hp _ rev7_plane51_mem) (hp _ rev7_plane69_mem) hx0 hx1
theorem rev7_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev7_planes) : rev7_s0_ll.real.1≤p.1 := by
  have hc := rev7_plane0.combine_sound rev7_plane0 1 0 (by decide) (by decide) p
    (hp _ rev7_plane0_mem) (hp _ rev7_plane0_mem)
  exact (rev7_plane0.combine rev7_plane0 1 0).xBoundCheck_sound rev7_s0_ll.nx rev7_s0_ll.dx true (by decide) p hc
theorem rev7_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev7_planes) : p.1≤rev7_s3_lr.real.1 := by
  have hc := rev7_plane51.combine_sound rev7_plane69 2129316000000 202532000000 (by decide) (by decide) p
    (hp _ rev7_plane51_mem) (hp _ rev7_plane69_mem)
  exact (rev7_plane51.combine rev7_plane69 2129316000000 202532000000).xBoundCheck_sound rev7_s3_lr.nx rev7_s3_lr.dx false (by decide) p hc
theorem rev7_hull (p : Point) (hp : p∈IntegerCarrier rev7_planes) :
    p∈rationalHull (fractionRow7.map FractionPoint.rational) := by
  have hxlo := rev7_bound0_lo p hp
  have hxhi := rev7_bound0_hi p hp
  by_cases h0 : p.1≤rev7_s0_lr.real.1
  · exact rev7_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev7_s1_lr.real.1
  · exact rev7_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev7_s2_lr.real.1
  · exact rev7_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev7_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull7 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,3,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow7 := by
  rw [← fractionRow7_correct]
  exact rev7_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull7
