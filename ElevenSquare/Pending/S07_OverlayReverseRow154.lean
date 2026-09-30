import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev154_planes : List IntegerPlane := integerOverlayPlanes ![10,10,9,6]
def rev154_plane13 : IntegerPlane := ⟨(-2112812000000),(-824716000000),(-1573757164456)⟩
theorem rev154_plane13_mem : rev154_plane13 ∈ rev154_planes := by decide
def rev154_plane17 : IntegerPlane := ⟨(-2099728000000),1393416000000,33871860516⟩
theorem rev154_plane17_mem : rev154_plane17 ∈ rev154_planes := by decide
def rev154_plane33 : IntegerPlane := ⟨2112812000000,(-824716000000),539054835544⟩
theorem rev154_plane33_mem : rev154_plane33 ∈ rev154_planes := by decide
def rev154_plane37 : IntegerPlane := ⟨2099728000000,1393416000000,2133599860516⟩
theorem rev154_plane37_mem : rev154_plane37 ∈ rev154_planes := by decide
def rev154_plane48 : IntegerPlane := ⟨(-1468788000000),2093220000000,880675273104⟩
theorem rev154_plane48_mem : rev154_plane48 ∈ rev154_planes := by decide
def rev154_plane75 : IntegerPlane := ⟨1468788000000,2093220000000,2349463273104⟩
theorem rev154_plane75_mem : rev154_plane75 ∈ rev154_planes := by decide
def rev154_vertex0 : FractionPoint := fractionRow154[0]!
theorem rev154_vertex0_mem : rev154_vertex0∈fractionRow154 := by decide
def rev154_vertex1 : FractionPoint := fractionRow154[1]!
theorem rev154_vertex1_mem : rev154_vertex1∈fractionRow154 := by decide
def rev154_vertex2 : FractionPoint := fractionRow154[2]!
theorem rev154_vertex2_mem : rev154_vertex2∈fractionRow154 := by decide
def rev154_vertex3 : FractionPoint := fractionRow154[3]!
theorem rev154_vertex3_mem : rev154_vertex3∈fractionRow154 := by decide
def rev154_vertex4 : FractionPoint := fractionRow154[4]!
theorem rev154_vertex4_mem : rev154_vertex4∈fractionRow154 := by decide
def rev154_vertex5 : FractionPoint := fractionRow154[5]!
theorem rev154_vertex5_mem : rev154_vertex5∈fractionRow154 := by decide
def rev154_s0_ll : FractionPoint := ⟨27062046846878853,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev154_s0_ll_mem : rev154_s0_ll.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane13 rev154_vertex1 rev154_vertex2 rev154_s0_ll
    rev154_vertex1_mem rev154_vertex2_mem (by decide)
def rev154_s0_lr : FractionPoint := ⟨8029484447765151,16309444058000000,2175578334880063446959,3362664866434382000000⟩
theorem rev154_s0_lr_mem : rev154_s0_lr.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane13 rev154_vertex1 rev154_vertex2 rev154_s0_lr
    rev154_vertex1_mem rev154_vertex2_mem (by decide)
def rev154_s0_ul : FractionPoint := ⟨27062046846878853,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev154_s0_ul_mem : rev154_s0_ul.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane17 rev154_vertex1 rev154_vertex0 rev154_s0_ul
    rev154_vertex1_mem rev154_vertex0_mem (by decide)
def rev154_s0_ur : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev154_s0_ur_mem : rev154_s0_ur.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane17 rev154_vertex1 rev154_vertex0 rev154_s0_ur
    rev154_vertex1_mem rev154_vertex0_mem (by decide)
theorem rev154_slab0 (p : Point) (hp : p∈IntegerCarrier rev154_planes)
    (hx0 : rev154_s0_ll.real.1≤p.1) (hx1 : p.1≤rev154_s0_lr.real.1) :
    p∈rationalHull (fractionRow154.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev154_plane13 rev154_plane17 rev154_s0_ll rev154_s0_lr rev154_s0_ul rev154_s0_ur
    (by decide) rev154_s0_ll_mem rev154_s0_lr_mem rev154_s0_ul_mem rev154_s0_ur_mem p
    (hp _ rev154_plane13_mem) (hp _ rev154_plane17_mem) hx0 hx1
def rev154_s1_ll : FractionPoint := ⟨8029484447765151,16309444058000000,2175578334880063446959,3362664866434382000000⟩
theorem rev154_s1_ll_mem : rev154_s1_ll.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane13 rev154_vertex1 rev154_vertex2 rev154_s1_ll
    rev154_vertex1_mem rev154_vertex2_mem (by decide)
def rev154_s1_lr : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev154_s1_lr_mem : rev154_s1_lr.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane13 rev154_vertex1 rev154_vertex2 rev154_s1_lr
    rev154_vertex1_mem rev154_vertex2_mem (by decide)
def rev154_s1_ul : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev154_s1_ul_mem : rev154_s1_ul.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane48 rev154_vertex0 rev154_vertex5 rev154_s1_ul
    rev154_vertex0_mem rev154_vertex5_mem (by decide)
def rev154_s1_ur : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev154_s1_ur_mem : rev154_s1_ur.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane48 rev154_vertex0 rev154_vertex5 rev154_s1_ur
    rev154_vertex0_mem rev154_vertex5_mem (by decide)
theorem rev154_slab1 (p : Point) (hp : p∈IntegerCarrier rev154_planes)
    (hx0 : rev154_s1_ll.real.1≤p.1) (hx1 : p.1≤rev154_s1_lr.real.1) :
    p∈rationalHull (fractionRow154.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev154_plane13 rev154_plane48 rev154_s1_ll rev154_s1_lr rev154_s1_ul rev154_s1_ur
    (by decide) rev154_s1_ll_mem rev154_s1_lr_mem rev154_s1_ul_mem rev154_s1_ur_mem p
    (hp _ rev154_plane13_mem) (hp _ rev154_plane48_mem) hx0 hx1
def rev154_s2_ll : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev154_s2_ll_mem : rev154_s2_ll.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane33 rev154_vertex2 rev154_vertex3 rev154_s2_ll
    rev154_vertex2_mem rev154_vertex3_mem (by decide)
def rev154_s2_lr : FractionPoint := ⟨8279959610234849,16309444058000000,2175578334880063446959,3362664866434382000000⟩
theorem rev154_s2_lr_mem : rev154_s2_lr.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane33 rev154_vertex2 rev154_vertex3 rev154_s2_lr
    rev154_vertex2_mem rev154_vertex3_mem (by decide)
def rev154_s2_ul : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev154_s2_ul_mem : rev154_s2_ul.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane75 rev154_vertex5 rev154_vertex4 rev154_s2_ul
    rev154_vertex5_mem rev154_vertex4_mem (by decide)
def rev154_s2_ur : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev154_s2_ur_mem : rev154_s2_ur.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane75 rev154_vertex5 rev154_vertex4 rev154_s2_ur
    rev154_vertex5_mem rev154_vertex4_mem (by decide)
theorem rev154_slab2 (p : Point) (hp : p∈IntegerCarrier rev154_planes)
    (hx0 : rev154_s2_ll.real.1≤p.1) (hx1 : p.1≤rev154_s2_lr.real.1) :
    p∈rationalHull (fractionRow154.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev154_plane33 rev154_plane75 rev154_s2_ll rev154_s2_lr rev154_s2_ul rev154_s2_ur
    (by decide) rev154_s2_ll_mem rev154_s2_lr_mem rev154_s2_ul_mem rev154_s2_ur_mem p
    (hp _ rev154_plane33_mem) (hp _ rev154_plane75_mem) hx0 hx1
def rev154_s3_ll : FractionPoint := ⟨8279959610234849,16309444058000000,2175578334880063446959,3362664866434382000000⟩
theorem rev154_s3_ll_mem : rev154_s3_ll.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane33 rev154_vertex2 rev154_vertex3 rev154_s3_ll
    rev154_vertex2_mem rev154_vertex3_mem (by decide)
def rev154_s3_lr : FractionPoint := ⟨31384269691121147,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev154_s3_lr_mem : rev154_s3_lr.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane33 rev154_vertex2 rev154_vertex3 rev154_s3_lr
    rev154_vertex2_mem rev154_vertex3_mem (by decide)
def rev154_s3_ul : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev154_s3_ul_mem : rev154_s3_ul.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane37 rev154_vertex4 rev154_vertex3 rev154_s3_ul
    rev154_vertex4_mem rev154_vertex3_mem (by decide)
def rev154_s3_ur : FractionPoint := ⟨31384269691121147,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev154_s3_ur_mem : rev154_s3_ur.real ∈ rationalHull (fractionRow154.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow154 rev154_plane37 rev154_vertex4 rev154_vertex3 rev154_s3_ur
    rev154_vertex4_mem rev154_vertex3_mem (by decide)
theorem rev154_slab3 (p : Point) (hp : p∈IntegerCarrier rev154_planes)
    (hx0 : rev154_s3_ll.real.1≤p.1) (hx1 : p.1≤rev154_s3_lr.real.1) :
    p∈rationalHull (fractionRow154.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev154_plane33 rev154_plane37 rev154_s3_ll rev154_s3_lr rev154_s3_ul rev154_s3_ur
    (by decide) rev154_s3_ll_mem rev154_s3_lr_mem rev154_s3_ul_mem rev154_s3_ur_mem p
    (hp _ rev154_plane33_mem) (hp _ rev154_plane37_mem) hx0 hx1
theorem rev154_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev154_planes) : rev154_s0_ll.real.1≤p.1 := by
  have hc := rev154_plane13.combine_sound rev154_plane17 1393416000000 824716000000 (by decide) (by decide) p
    (hp _ rev154_plane13_mem) (hp _ rev154_plane17_mem)
  exact (rev154_plane13.combine rev154_plane17 1393416000000 824716000000).xBoundCheck_sound rev154_s0_ll.nx rev154_s0_ll.dx true (by decide) p hc
theorem rev154_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev154_planes) : p.1≤rev154_s3_lr.real.1 := by
  have hc := rev154_plane33.combine_sound rev154_plane37 1393416000000 824716000000 (by decide) (by decide) p
    (hp _ rev154_plane33_mem) (hp _ rev154_plane37_mem)
  exact (rev154_plane33.combine rev154_plane37 1393416000000 824716000000).xBoundCheck_sound rev154_s3_lr.nx rev154_s3_lr.dx false (by decide) p hc
theorem rev154_hull (p : Point) (hp : p∈IntegerCarrier rev154_planes) :
    p∈rationalHull (fractionRow154.map FractionPoint.rational) := by
  have hxlo := rev154_bound0_lo p hp
  have hxhi := rev154_bound0_hi p hp
  by_cases h0 : p.1≤rev154_s0_lr.real.1
  · exact rev154_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev154_s1_lr.real.1
  · exact rev154_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev154_s2_lr.real.1
  · exact rev154_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev154_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull154 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,10,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow154 := by
  rw [← fractionRow154_correct]
  exact rev154_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull154
