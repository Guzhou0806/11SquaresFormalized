import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev70_planes : List IntegerPlane := integerOverlayPlanes ![5,6,6,9]
def rev70_plane10 : IntegerPlane := ⟨2112812000000,824716000000,1363770835544⟩
theorem rev70_plane10_mem : rev70_plane10 ∈ rev70_planes := by decide
def rev70_plane13 : IntegerPlane := ⟨(-51300000000),2168356000000,953534835544⟩
theorem rev70_plane13_mem : rev70_plane13 ∈ rev70_planes := by decide
def rev70_plane26 : IntegerPlane := ⟨13084000000,(-2218132000000),(-610502975028)⟩
theorem rev70_plane26_mem : rev70_plane26 ∈ rev70_planes := by decide
def rev70_plane29 : IntegerPlane := ⟨2112812000000,(-824716000000),749041164456⟩
theorem rev70_plane29_mem : rev70_plane29 ∈ rev70_planes := by decide
def rev70_plane69 : IntegerPlane := ⟨(-2168356000000),51300000000,(-953534835544)⟩
theorem rev70_plane69_mem : rev70_plane69 ∈ rev70_planes := by decide
def rev70_vertex0 : FractionPoint := fractionRow70[0]!
theorem rev70_vertex0_mem : rev70_vertex0∈fractionRow70 := by decide
def rev70_vertex1 : FractionPoint := fractionRow70[1]!
theorem rev70_vertex1_mem : rev70_vertex1∈fractionRow70 := by decide
def rev70_vertex2 : FractionPoint := fractionRow70[2]!
theorem rev70_vertex2_mem : rev70_vertex2∈fractionRow70 := by decide
def rev70_vertex3 : FractionPoint := fractionRow70[3]!
theorem rev70_vertex3_mem : rev70_vertex3∈fractionRow70 := by decide
def rev70_vertex4 : FractionPoint := fractionRow70[4]!
theorem rev70_vertex4_mem : rev70_vertex4∈fractionRow70 := by decide
def rev70_s0_ll : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev70_s0_ll_mem : rev70_s0_ll.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane26 rev70_vertex0 rev70_vertex1 rev70_s0_ll
    rev70_vertex0_mem rev70_vertex1_mem (by decide)
def rev70_s0_lr : FractionPoint := ⟨6273255497,13928000000,2146291177778183,7723535624000000⟩
theorem rev70_s0_lr_mem : rev70_s0_lr.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane26 rev70_vertex0 rev70_vertex1 rev70_s0_lr
    rev70_vertex0_mem rev70_vertex1_mem (by decide)
def rev70_s0_ul : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev70_s0_ul_mem : rev70_s0_ul.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane69 rev70_vertex0 rev70_vertex4 rev70_s0_ul
    rev70_vertex0_mem rev70_vertex4_mem (by decide)
def rev70_s0_ur : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev70_s0_ur_mem : rev70_s0_ur.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane69 rev70_vertex0 rev70_vertex4 rev70_s0_ur
    rev70_vertex0_mem rev70_vertex4_mem (by decide)
theorem rev70_slab0 (p : Point) (hp : p∈IntegerCarrier rev70_planes)
    (hx0 : rev70_s0_ll.real.1≤p.1) (hx1 : p.1≤rev70_s0_lr.real.1) :
    p∈rationalHull (fractionRow70.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev70_plane26 rev70_plane69 rev70_s0_ll rev70_s0_lr rev70_s0_ul rev70_s0_ur
    (by decide) rev70_s0_ll_mem rev70_s0_lr_mem rev70_s0_ul_mem rev70_s0_ur_mem p
    (hp _ rev70_plane26_mem) (hp _ rev70_plane69_mem) hx0 hx1
def rev70_s1_ll : FractionPoint := ⟨6273255497,13928000000,2146291177778183,7723535624000000⟩
theorem rev70_s1_ll_mem : rev70_s1_ll.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane26 rev70_vertex0 rev70_vertex1 rev70_s1_ll
    rev70_vertex0_mem rev70_vertex1_mem (by decide)
def rev70_s1_lr : FractionPoint := ⟨27062046846878853,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev70_s1_lr_mem : rev70_s1_lr.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane26 rev70_vertex0 rev70_vertex1 rev70_s1_lr
    rev70_vertex0_mem rev70_vertex1_mem (by decide)
def rev70_s1_ul : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev70_s1_ul_mem : rev70_s1_ul.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane13 rev70_vertex4 rev70_vertex3 rev70_s1_ul
    rev70_vertex4_mem rev70_vertex3_mem (by decide)
def rev70_s1_ur : FractionPoint := ⟨27062046846878853,58446316538000000,751564234624464244547,1667531857145678000000⟩
theorem rev70_s1_ur_mem : rev70_s1_ur.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane13 rev70_vertex4 rev70_vertex3 rev70_s1_ur
    rev70_vertex4_mem rev70_vertex3_mem (by decide)
theorem rev70_slab1 (p : Point) (hp : p∈IntegerCarrier rev70_planes)
    (hx0 : rev70_s1_ll.real.1≤p.1) (hx1 : p.1≤rev70_s1_lr.real.1) :
    p∈rationalHull (fractionRow70.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev70_plane26 rev70_plane13 rev70_s1_ll rev70_s1_lr rev70_s1_ul rev70_s1_ur
    (by decide) rev70_s1_ll_mem rev70_s1_lr_mem rev70_s1_ul_mem rev70_s1_ur_mem p
    (hp _ rev70_plane26_mem) (hp _ rev70_plane13_mem) hx0 hx1
def rev70_s2_ll : FractionPoint := ⟨27062046846878853,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev70_s2_ll_mem : rev70_s2_ll.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane29 rev70_vertex1 rev70_vertex2 rev70_s2_ll
    rev70_vertex1_mem rev70_vertex2_mem (by decide)
def rev70_s2_lr : FractionPoint := ⟨357030466849727,760466530900000,28862112326649171349,97995143046519437500⟩
theorem rev70_s2_lr_mem : rev70_s2_lr.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane29 rev70_vertex1 rev70_vertex2 rev70_s2_lr
    rev70_vertex1_mem rev70_vertex2_mem (by decide)
def rev70_s2_ul : FractionPoint := ⟨27062046846878853,58446316538000000,751564234624464244547,1667531857145678000000⟩
theorem rev70_s2_ul_mem : rev70_s2_ul.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane13 rev70_vertex4 rev70_vertex3 rev70_s2_ul
    rev70_vertex4_mem rev70_vertex3_mem (by decide)
def rev70_s2_ur : FractionPoint := ⟨357030466849727,760466530900000,857155134382729,1901166327250000⟩
theorem rev70_s2_ur_mem : rev70_s2_ur.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane13 rev70_vertex4 rev70_vertex3 rev70_s2_ur
    rev70_vertex4_mem rev70_vertex3_mem (by decide)
theorem rev70_slab2 (p : Point) (hp : p∈IntegerCarrier rev70_planes)
    (hx0 : rev70_s2_ll.real.1≤p.1) (hx1 : p.1≤rev70_s2_lr.real.1) :
    p∈rationalHull (fractionRow70.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev70_plane29 rev70_plane13 rev70_s2_ll rev70_s2_lr rev70_s2_ul rev70_s2_ur
    (by decide) rev70_s2_ll_mem rev70_s2_lr_mem rev70_s2_ul_mem rev70_s2_ur_mem p
    (hp _ rev70_plane29_mem) (hp _ rev70_plane13_mem) hx0 hx1
def rev70_s3_ll : FractionPoint := ⟨357030466849727,760466530900000,28862112326649171349,97995143046519437500⟩
theorem rev70_s3_ll_mem : rev70_s3_ll.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane29 rev70_vertex1 rev70_vertex2 rev70_s3_ll
    rev70_vertex1_mem rev70_vertex2_mem (by decide)
def rev70_s3_lr : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev70_s3_lr_mem : rev70_s3_lr.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane29 rev70_vertex1 rev70_vertex2 rev70_s3_lr
    rev70_vertex1_mem rev70_vertex2_mem (by decide)
def rev70_s3_ul : FractionPoint := ⟨357030466849727,760466530900000,857155134382729,1901166327250000⟩
theorem rev70_s3_ul_mem : rev70_s3_ul.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane10 rev70_vertex3 rev70_vertex2 rev70_s3_ul
    rev70_vertex3_mem rev70_vertex2_mem (by decide)
def rev70_s3_ur : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev70_s3_ur_mem : rev70_s3_ur.real ∈ rationalHull (fractionRow70.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow70 rev70_plane10 rev70_vertex3 rev70_vertex2 rev70_s3_ur
    rev70_vertex3_mem rev70_vertex2_mem (by decide)
theorem rev70_slab3 (p : Point) (hp : p∈IntegerCarrier rev70_planes)
    (hx0 : rev70_s3_ll.real.1≤p.1) (hx1 : p.1≤rev70_s3_lr.real.1) :
    p∈rationalHull (fractionRow70.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev70_plane29 rev70_plane10 rev70_s3_ll rev70_s3_lr rev70_s3_ul rev70_s3_ur
    (by decide) rev70_s3_ll_mem rev70_s3_lr_mem rev70_s3_ul_mem rev70_s3_ur_mem p
    (hp _ rev70_plane29_mem) (hp _ rev70_plane10_mem) hx0 hx1
theorem rev70_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev70_planes) : rev70_s0_ll.real.1≤p.1 := by
  have hc := rev70_plane26.combine_sound rev70_plane69 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev70_plane26_mem) (hp _ rev70_plane69_mem)
  exact (rev70_plane26.combine rev70_plane69 51300000000 2218132000000).xBoundCheck_sound rev70_s0_ll.nx rev70_s0_ll.dx true (by decide) p hc
theorem rev70_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev70_planes) : p.1≤rev70_s3_lr.real.1 := by
  have hc := rev70_plane10.combine_sound rev70_plane29 824716000000 824716000000 (by decide) (by decide) p
    (hp _ rev70_plane10_mem) (hp _ rev70_plane29_mem)
  exact (rev70_plane10.combine rev70_plane29 824716000000 824716000000).xBoundCheck_sound rev70_s3_lr.nx rev70_s3_lr.dx false (by decide) p hc
theorem rev70_hull (p : Point) (hp : p∈IntegerCarrier rev70_planes) :
    p∈rationalHull (fractionRow70.map FractionPoint.rational) := by
  have hxlo := rev70_bound0_lo p hp
  have hxhi := rev70_bound0_hi p hp
  by_cases h0 : p.1≤rev70_s0_lr.real.1
  · exact rev70_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev70_s1_lr.real.1
  · exact rev70_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev70_s2_lr.real.1
  · exact rev70_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev70_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull70 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,6,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow70 := by
  rw [← fractionRow70_correct]
  exact rev70_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull70
