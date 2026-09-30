import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev65_planes : List IntegerPlane := integerOverlayPlanes ![5,5,6,9]
def rev65_plane6 : IntegerPlane := ⟨2099728000000,(-1393416000000),740183860516⟩
theorem rev65_plane6_mem : rev65_plane6 ∈ rev65_planes := by decide
def rev65_plane10 : IntegerPlane := ⟨2112812000000,824716000000,1363770835544⟩
theorem rev65_plane10_mem : rev65_plane10 ∈ rev65_planes := by decide
def rev65_plane26 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-1359544139484)⟩
theorem rev65_plane26_mem : rev65_plane26 ∈ rev65_planes := by decide
def rev65_plane30 : IntegerPlane := ⟨(-2112812000000),824716000000,(-749041164456)⟩
theorem rev65_plane30_mem : rev65_plane30 ∈ rev65_planes := by decide
def rev65_plane55 : IntegerPlane := ⟨1468788000000,(-2093220000000),256243273104⟩
theorem rev65_plane55_mem : rev65_plane55 ∈ rev65_planes := by decide
def rev65_plane68 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-1212544726896)⟩
theorem rev65_plane68_mem : rev65_plane68 ∈ rev65_planes := by decide
def rev65_vertex0 : FractionPoint := fractionRow65[0]!
theorem rev65_vertex0_mem : rev65_vertex0∈fractionRow65 := by decide
def rev65_vertex1 : FractionPoint := fractionRow65[1]!
theorem rev65_vertex1_mem : rev65_vertex1∈fractionRow65 := by decide
def rev65_vertex2 : FractionPoint := fractionRow65[2]!
theorem rev65_vertex2_mem : rev65_vertex2∈fractionRow65 := by decide
def rev65_vertex3 : FractionPoint := fractionRow65[3]!
theorem rev65_vertex3_mem : rev65_vertex3∈fractionRow65 := by decide
def rev65_vertex4 : FractionPoint := fractionRow65[4]!
theorem rev65_vertex4_mem : rev65_vertex4∈fractionRow65 := by decide
def rev65_vertex5 : FractionPoint := fractionRow65[5]!
theorem rev65_vertex5_mem : rev65_vertex5∈fractionRow65 := by decide
def rev65_s0_ll : FractionPoint := ⟨27062046846878853,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev65_s0_ll_mem : rev65_s0_ll.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane26 rev65_vertex3 rev65_vertex4 rev65_s0_ll
    rev65_vertex3_mem rev65_vertex4_mem (by decide)
def rev65_s0_lr : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev65_s0_lr_mem : rev65_s0_lr.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane26 rev65_vertex3 rev65_vertex4 rev65_s0_lr
    rev65_vertex3_mem rev65_vertex4_mem (by decide)
def rev65_s0_ul : FractionPoint := ⟨27062046846878853,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev65_s0_ul_mem : rev65_s0_ul.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane30 rev65_vertex3 rev65_vertex2 rev65_s0_ul
    rev65_vertex3_mem rev65_vertex2_mem (by decide)
def rev65_s0_ur : FractionPoint := ⟨8029484447765151,16309444058000000,1187086531554318553041,3362664866434382000000⟩
theorem rev65_s0_ur_mem : rev65_s0_ur.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane30 rev65_vertex3 rev65_vertex2 rev65_s0_ur
    rev65_vertex3_mem rev65_vertex2_mem (by decide)
theorem rev65_slab0 (p : Point) (hp : p∈IntegerCarrier rev65_planes)
    (hx0 : rev65_s0_ll.real.1≤p.1) (hx1 : p.1≤rev65_s0_lr.real.1) :
    p∈rationalHull (fractionRow65.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev65_plane26 rev65_plane30 rev65_s0_ll rev65_s0_lr rev65_s0_ul rev65_s0_ur
    (by decide) rev65_s0_ll_mem rev65_s0_lr_mem rev65_s0_ul_mem rev65_s0_ur_mem p
    (hp _ rev65_plane26_mem) (hp _ rev65_plane30_mem) hx0 hx1
def rev65_s1_ll : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev65_s1_ll_mem : rev65_s1_ll.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane68 rev65_vertex4 rev65_vertex5 rev65_s1_ll
    rev65_vertex4_mem rev65_vertex5_mem (by decide)
def rev65_s1_lr : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev65_s1_lr_mem : rev65_s1_lr.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane68 rev65_vertex4 rev65_vertex5 rev65_s1_lr
    rev65_vertex4_mem rev65_vertex5_mem (by decide)
def rev65_s1_ul : FractionPoint := ⟨8029484447765151,16309444058000000,1187086531554318553041,3362664866434382000000⟩
theorem rev65_s1_ul_mem : rev65_s1_ul.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane30 rev65_vertex3 rev65_vertex2 rev65_s1_ul
    rev65_vertex3_mem rev65_vertex2_mem (by decide)
def rev65_s1_ur : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev65_s1_ur_mem : rev65_s1_ur.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane30 rev65_vertex3 rev65_vertex2 rev65_s1_ur
    rev65_vertex3_mem rev65_vertex2_mem (by decide)
theorem rev65_slab1 (p : Point) (hp : p∈IntegerCarrier rev65_planes)
    (hx0 : rev65_s1_ll.real.1≤p.1) (hx1 : p.1≤rev65_s1_lr.real.1) :
    p∈rationalHull (fractionRow65.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev65_plane68 rev65_plane30 rev65_s1_ll rev65_s1_lr rev65_s1_ul rev65_s1_ur
    (by decide) rev65_s1_ll_mem rev65_s1_lr_mem rev65_s1_ul_mem rev65_s1_ur_mem p
    (hp _ rev65_plane68_mem) (hp _ rev65_plane30_mem) hx0 hx1
def rev65_s2_ll : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev65_s2_ll_mem : rev65_s2_ll.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane55 rev65_vertex5 rev65_vertex0 rev65_s2_ll
    rev65_vertex5_mem rev65_vertex0_mem (by decide)
def rev65_s2_lr : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev65_s2_lr_mem : rev65_s2_lr.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane55 rev65_vertex5 rev65_vertex0 rev65_s2_lr
    rev65_vertex5_mem rev65_vertex0_mem (by decide)
def rev65_s2_ul : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev65_s2_ul_mem : rev65_s2_ul.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane10 rev65_vertex2 rev65_vertex1 rev65_s2_ul
    rev65_vertex2_mem rev65_vertex1_mem (by decide)
def rev65_s2_ur : FractionPoint := ⟨8279959610234849,16309444058000000,1187086531554318553041,3362664866434382000000⟩
theorem rev65_s2_ur_mem : rev65_s2_ur.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane10 rev65_vertex2 rev65_vertex1 rev65_s2_ur
    rev65_vertex2_mem rev65_vertex1_mem (by decide)
theorem rev65_slab2 (p : Point) (hp : p∈IntegerCarrier rev65_planes)
    (hx0 : rev65_s2_ll.real.1≤p.1) (hx1 : p.1≤rev65_s2_lr.real.1) :
    p∈rationalHull (fractionRow65.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev65_plane55 rev65_plane10 rev65_s2_ll rev65_s2_lr rev65_s2_ul rev65_s2_ur
    (by decide) rev65_s2_ll_mem rev65_s2_lr_mem rev65_s2_ul_mem rev65_s2_ur_mem p
    (hp _ rev65_plane55_mem) (hp _ rev65_plane10_mem) hx0 hx1
def rev65_s3_ll : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev65_s3_ll_mem : rev65_s3_ll.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane6 rev65_vertex0 rev65_vertex1 rev65_s3_ll
    rev65_vertex0_mem rev65_vertex1_mem (by decide)
def rev65_s3_lr : FractionPoint := ⟨31384269691121147,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev65_s3_lr_mem : rev65_s3_lr.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane6 rev65_vertex0 rev65_vertex1 rev65_s3_lr
    rev65_vertex0_mem rev65_vertex1_mem (by decide)
def rev65_s3_ul : FractionPoint := ⟨8279959610234849,16309444058000000,1187086531554318553041,3362664866434382000000⟩
theorem rev65_s3_ul_mem : rev65_s3_ul.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane10 rev65_vertex2 rev65_vertex1 rev65_s3_ul
    rev65_vertex2_mem rev65_vertex1_mem (by decide)
def rev65_s3_ur : FractionPoint := ⟨31384269691121147,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev65_s3_ur_mem : rev65_s3_ur.real ∈ rationalHull (fractionRow65.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow65 rev65_plane10 rev65_vertex2 rev65_vertex1 rev65_s3_ur
    rev65_vertex2_mem rev65_vertex1_mem (by decide)
theorem rev65_slab3 (p : Point) (hp : p∈IntegerCarrier rev65_planes)
    (hx0 : rev65_s3_ll.real.1≤p.1) (hx1 : p.1≤rev65_s3_lr.real.1) :
    p∈rationalHull (fractionRow65.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev65_plane6 rev65_plane10 rev65_s3_ll rev65_s3_lr rev65_s3_ul rev65_s3_ur
    (by decide) rev65_s3_ll_mem rev65_s3_lr_mem rev65_s3_ul_mem rev65_s3_ur_mem p
    (hp _ rev65_plane6_mem) (hp _ rev65_plane10_mem) hx0 hx1
theorem rev65_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev65_planes) : rev65_s0_ll.real.1≤p.1 := by
  have hc := rev65_plane26.combine_sound rev65_plane30 824716000000 1393416000000 (by decide) (by decide) p
    (hp _ rev65_plane26_mem) (hp _ rev65_plane30_mem)
  exact (rev65_plane26.combine rev65_plane30 824716000000 1393416000000).xBoundCheck_sound rev65_s0_ll.nx rev65_s0_ll.dx true (by decide) p hc
theorem rev65_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev65_planes) : p.1≤rev65_s3_lr.real.1 := by
  have hc := rev65_plane6.combine_sound rev65_plane10 824716000000 1393416000000 (by decide) (by decide) p
    (hp _ rev65_plane6_mem) (hp _ rev65_plane10_mem)
  exact (rev65_plane6.combine rev65_plane10 824716000000 1393416000000).xBoundCheck_sound rev65_s3_lr.nx rev65_s3_lr.dx false (by decide) p hc
theorem rev65_hull (p : Point) (hp : p∈IntegerCarrier rev65_planes) :
    p∈rationalHull (fractionRow65.map FractionPoint.rational) := by
  have hxlo := rev65_bound0_lo p hp
  have hxhi := rev65_bound0_hi p hp
  by_cases h0 : p.1≤rev65_s0_lr.real.1
  · exact rev65_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev65_s1_lr.real.1
  · exact rev65_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev65_s2_lr.real.1
  · exact rev65_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev65_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull65 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,5,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow65 := by
  rw [← fractionRow65_correct]
  exact rev65_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull65
