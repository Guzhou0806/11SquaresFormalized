import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev130_planes : List IntegerPlane := integerOverlayPlanes ![9,6,5,6]
def rev130_plane34 : IntegerPlane := ⟨51300000000,2168356000000,1214821164456⟩
theorem rev130_plane34_mem : rev130_plane34 ∈ rev130_planes := by decide
def rev130_plane50 : IntegerPlane := ⟨824716000000,(-2112812000000),(-749041164456)⟩
theorem rev130_plane50_mem : rev130_plane50 ∈ rev130_planes := by decide
def rev130_plane53 : IntegerPlane := ⟨2168356000000,51300000000,1004834835544⟩
theorem rev130_plane53_mem : rev130_plane53 ∈ rev130_planes := by decide
def rev130_plane66 : IntegerPlane := ⟨(-2218132000000),(-13084000000),(-623586975028)⟩
theorem rev130_plane66_mem : rev130_plane66 ∈ rev130_planes := by decide
def rev130_plane69 : IntegerPlane := ⟨(-824716000000),(-2112812000000),(-1363770835544)⟩
theorem rev130_plane69_mem : rev130_plane69 ∈ rev130_planes := by decide
def rev130_vertex0 : FractionPoint := fractionRow130[0]!
theorem rev130_vertex0_mem : rev130_vertex0∈fractionRow130 := by decide
def rev130_vertex1 : FractionPoint := fractionRow130[1]!
theorem rev130_vertex1_mem : rev130_vertex1∈fractionRow130 := by decide
def rev130_vertex2 : FractionPoint := fractionRow130[2]!
theorem rev130_vertex2_mem : rev130_vertex2∈fractionRow130 := by decide
def rev130_vertex3 : FractionPoint := fractionRow130[3]!
theorem rev130_vertex3_mem : rev130_vertex3∈fractionRow130 := by decide
def rev130_vertex4 : FractionPoint := fractionRow130[4]!
theorem rev130_vertex4_mem : rev130_vertex4∈fractionRow130 := by decide
def rev130_s0_ll : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev130_s0_ll_mem : rev130_s0_ll.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane66 rev130_vertex3 rev130_vertex4 rev130_s0_ll
    rev130_vertex3_mem rev130_vertex4_mem (by decide)
def rev130_s0_lr : FractionPoint := ⟨16245980828382513,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev130_s0_lr_mem : rev130_s0_lr.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane66 rev130_vertex3 rev130_vertex4 rev130_s0_lr
    rev130_vertex3_mem rev130_vertex4_mem (by decide)
def rev130_s0_ul : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev130_s0_ul_mem : rev130_s0_ul.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane34 rev130_vertex3 rev130_vertex2 rev130_s0_ul
    rev130_vertex3_mem rev130_vertex2_mem (by decide)
def rev130_s0_ur : FractionPoint := ⟨16245980828382513,58446316538000000,923268467083698784953,1667531857145678000000⟩
theorem rev130_s0_ur_mem : rev130_s0_ur.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane34 rev130_vertex3 rev130_vertex2 rev130_s0_ur
    rev130_vertex3_mem rev130_vertex2_mem (by decide)
theorem rev130_slab0 (p : Point) (hp : p∈IntegerCarrier rev130_planes)
    (hx0 : rev130_s0_ll.real.1≤p.1) (hx1 : p.1≤rev130_s0_lr.real.1) :
    p∈rationalHull (fractionRow130.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev130_plane66 rev130_plane34 rev130_s0_ll rev130_s0_lr rev130_s0_ul rev130_s0_ur
    (by decide) rev130_s0_ll_mem rev130_s0_lr_mem rev130_s0_ul_mem rev130_s0_ur_mem p
    (hp _ rev130_plane66_mem) (hp _ rev130_plane34_mem) hx0 hx1
def rev130_s1_ll : FractionPoint := ⟨16245980828382513,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev130_s1_ll_mem : rev130_s1_ll.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane69 rev130_vertex4 rev130_vertex0 rev130_s1_ll
    rev130_vertex4_mem rev130_vertex0_mem (by decide)
def rev130_s1_lr : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev130_s1_lr_mem : rev130_s1_lr.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane69 rev130_vertex4 rev130_vertex0 rev130_s1_lr
    rev130_vertex4_mem rev130_vertex0_mem (by decide)
def rev130_s1_ul : FractionPoint := ⟨16245980828382513,58446316538000000,923268467083698784953,1667531857145678000000⟩
theorem rev130_s1_ul_mem : rev130_s1_ul.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane34 rev130_vertex3 rev130_vertex2 rev130_s1_ul
    rev130_vertex3_mem rev130_vertex2_mem (by decide)
def rev130_s1_ur : FractionPoint := ⟨38420604443,103089500000,405474767846253,735311631125000⟩
theorem rev130_s1_ur_mem : rev130_s1_ur.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane34 rev130_vertex3 rev130_vertex2 rev130_s1_ur
    rev130_vertex3_mem rev130_vertex2_mem (by decide)
theorem rev130_slab1 (p : Point) (hp : p∈IntegerCarrier rev130_planes)
    (hx0 : rev130_s1_ll.real.1≤p.1) (hx1 : p.1≤rev130_s1_lr.real.1) :
    p∈rationalHull (fractionRow130.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev130_plane69 rev130_plane34 rev130_s1_ll rev130_s1_lr rev130_s1_ul rev130_s1_ur
    (by decide) rev130_s1_ll_mem rev130_s1_lr_mem rev130_s1_ul_mem rev130_s1_ur_mem p
    (hp _ rev130_plane69_mem) (hp _ rev130_plane34_mem) hx0 hx1
def rev130_s2_ll : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev130_s2_ll_mem : rev130_s2_ll.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane50 rev130_vertex0 rev130_vertex1 rev130_s2_ll
    rev130_vertex0_mem rev130_vertex1_mem (by decide)
def rev130_s2_lr : FractionPoint := ⟨6273255497,13928000000,780314975950351,1471362276800000⟩
theorem rev130_s2_lr_mem : rev130_s2_lr.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane50 rev130_vertex0 rev130_vertex1 rev130_s2_lr
    rev130_vertex0_mem rev130_vertex1_mem (by decide)
def rev130_s2_ul : FractionPoint := ⟨38420604443,103089500000,405474767846253,735311631125000⟩
theorem rev130_s2_ul_mem : rev130_s2_ul.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane34 rev130_vertex3 rev130_vertex2 rev130_s2_ul
    rev130_vertex3_mem rev130_vertex2_mem (by decide)
def rev130_s2_ur : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev130_s2_ur_mem : rev130_s2_ur.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane34 rev130_vertex3 rev130_vertex2 rev130_s2_ur
    rev130_vertex3_mem rev130_vertex2_mem (by decide)
theorem rev130_slab2 (p : Point) (hp : p∈IntegerCarrier rev130_planes)
    (hx0 : rev130_s2_ll.real.1≤p.1) (hx1 : p.1≤rev130_s2_lr.real.1) :
    p∈rationalHull (fractionRow130.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev130_plane50 rev130_plane34 rev130_s2_ll rev130_s2_lr rev130_s2_ul rev130_s2_ur
    (by decide) rev130_s2_ll_mem rev130_s2_lr_mem rev130_s2_ul_mem rev130_s2_ur_mem p
    (hp _ rev130_plane50_mem) (hp _ rev130_plane34_mem) hx0 hx1
def rev130_s3_ll : FractionPoint := ⟨6273255497,13928000000,780314975950351,1471362276800000⟩
theorem rev130_s3_ll_mem : rev130_s3_ll.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane50 rev130_vertex0 rev130_vertex1 rev130_s3_ll
    rev130_vertex0_mem rev130_vertex1_mem (by decide)
def rev130_s3_lr : FractionPoint := ⟨857155134382729,1901166327250000,403436064050273,760466530900000⟩
theorem rev130_s3_lr_mem : rev130_s3_lr.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane50 rev130_vertex0 rev130_vertex1 rev130_s3_lr
    rev130_vertex0_mem rev130_vertex1_mem (by decide)
def rev130_s3_ul : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev130_s3_ul_mem : rev130_s3_ul.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane53 rev130_vertex2 rev130_vertex1 rev130_s3_ul
    rev130_vertex2_mem rev130_vertex1_mem (by decide)
def rev130_s3_ur : FractionPoint := ⟨857155134382729,1901166327250000,403436064050273,760466530900000⟩
theorem rev130_s3_ur_mem : rev130_s3_ur.real ∈ rationalHull (fractionRow130.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow130 rev130_plane53 rev130_vertex2 rev130_vertex1 rev130_s3_ur
    rev130_vertex2_mem rev130_vertex1_mem (by decide)
theorem rev130_slab3 (p : Point) (hp : p∈IntegerCarrier rev130_planes)
    (hx0 : rev130_s3_ll.real.1≤p.1) (hx1 : p.1≤rev130_s3_lr.real.1) :
    p∈rationalHull (fractionRow130.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev130_plane50 rev130_plane53 rev130_s3_ll rev130_s3_lr rev130_s3_ul rev130_s3_ur
    (by decide) rev130_s3_ll_mem rev130_s3_lr_mem rev130_s3_ul_mem rev130_s3_ur_mem p
    (hp _ rev130_plane50_mem) (hp _ rev130_plane53_mem) hx0 hx1
theorem rev130_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev130_planes) : rev130_s0_ll.real.1≤p.1 := by
  have hc := rev130_plane34.combine_sound rev130_plane66 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev130_plane34_mem) (hp _ rev130_plane66_mem)
  exact (rev130_plane34.combine rev130_plane66 13084000000 2168356000000).xBoundCheck_sound rev130_s0_ll.nx rev130_s0_ll.dx true (by decide) p hc
theorem rev130_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev130_planes) : p.1≤rev130_s3_lr.real.1 := by
  have hc := rev130_plane50.combine_sound rev130_plane53 51300000000 2112812000000 (by decide) (by decide) p
    (hp _ rev130_plane50_mem) (hp _ rev130_plane53_mem)
  exact (rev130_plane50.combine rev130_plane53 51300000000 2112812000000).xBoundCheck_sound rev130_s3_lr.nx rev130_s3_lr.dx false (by decide) p hc
theorem rev130_hull (p : Point) (hp : p∈IntegerCarrier rev130_planes) :
    p∈rationalHull (fractionRow130.map FractionPoint.rational) := by
  have hxlo := rev130_bound0_lo p hp
  have hxhi := rev130_bound0_hi p hp
  by_cases h0 : p.1≤rev130_s0_lr.real.1
  · exact rev130_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev130_s1_lr.real.1
  · exact rev130_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev130_s2_lr.real.1
  · exact rev130_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev130_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull130 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,5,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow130 := by
  rw [← fractionRow130_correct]
  exact rev130_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull130
