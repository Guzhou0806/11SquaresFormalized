import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks9
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev76_planes : List IntegerPlane := integerOverlayPlanes ![6,4,10,13]
def rev76_plane11 : IntegerPlane := ⟨2044968000000,(-643972000000),1318460524019⟩
theorem rev76_plane11_mem : rev76_plane11 ∈ rev76_planes := by decide
def rev76_plane15 : IntegerPlane := ⟨2093220000000,1468788000000,2349463273104⟩
theorem rev76_plane15_mem : rev76_plane15 ∈ rev76_planes := by decide
def rev76_plane29 : IntegerPlane := ⟨(-2144520000000),(-699568000000),(-1885510108648)⟩
theorem rev76_plane29_mem : rev76_plane29 ∈ rev76_planes := by decide
def rev76_plane33 : IntegerPlane := ⟨(-2093220000000),1468788000000,(-880675273104)⟩
theorem rev76_plane33_mem : rev76_plane33 ∈ rev76_planes := by decide
def rev76_plane74 : IntegerPlane := ⟨(-1393416000000),2099728000000,(-33871860516)⟩
theorem rev76_plane74_mem : rev76_plane74 ∈ rev76_planes := by decide
def rev76_vertex0 : FractionPoint := fractionRow76[0]!
theorem rev76_vertex0_mem : rev76_vertex0∈fractionRow76 := by decide
def rev76_vertex1 : FractionPoint := fractionRow76[1]!
theorem rev76_vertex1_mem : rev76_vertex1∈fractionRow76 := by decide
def rev76_vertex2 : FractionPoint := fractionRow76[2]!
theorem rev76_vertex2_mem : rev76_vertex2∈fractionRow76 := by decide
def rev76_vertex3 : FractionPoint := fractionRow76[3]!
theorem rev76_vertex3_mem : rev76_vertex3∈fractionRow76 := by decide
def rev76_vertex4 : FractionPoint := fractionRow76[4]!
theorem rev76_vertex4_mem : rev76_vertex4∈fractionRow76 := by decide
def rev76_s0_ll : FractionPoint := ⟨80699534251423,109987485000000,3270661284241,7332499000000⟩
theorem rev76_s0_ll_mem : rev76_s0_ll.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane29 rev76_vertex4 rev76_vertex0 rev76_s0_ll
    rev76_vertex4_mem rev76_vertex0_mem (by decide)
def rev76_s0_lr : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev76_s0_lr_mem : rev76_s0_lr.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane29 rev76_vertex4 rev76_vertex0 rev76_s0_lr
    rev76_vertex4_mem rev76_vertex0_mem (by decide)
def rev76_s0_ul : FractionPoint := ⟨80699534251423,109987485000000,3270661284241,7332499000000⟩
theorem rev76_s0_ul_mem : rev76_s0_ul.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane33 rev76_vertex4 rev76_vertex3 rev76_s0_ul
    rev76_vertex4_mem rev76_vertex3_mem (by decide)
def rev76_s0_ur : FractionPoint := ⟨1935297561189487,2546743666000000,150679115621052151573,311718877974734000000⟩
theorem rev76_s0_ur_mem : rev76_s0_ur.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane33 rev76_vertex4 rev76_vertex3 rev76_s0_ur
    rev76_vertex4_mem rev76_vertex3_mem (by decide)
theorem rev76_slab0 (p : Point) (hp : p∈IntegerCarrier rev76_planes)
    (hx0 : rev76_s0_ll.real.1≤p.1) (hx1 : p.1≤rev76_s0_lr.real.1) :
    p∈rationalHull (fractionRow76.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev76_plane29 rev76_plane33 rev76_s0_ll rev76_s0_lr rev76_s0_ul rev76_s0_ur
    (by decide) rev76_s0_ll_mem rev76_s0_lr_mem rev76_s0_ul_mem rev76_s0_ur_mem p
    (hp _ rev76_plane29_mem) (hp _ rev76_plane33_mem) hx0 hx1
def rev76_s1_ll : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev76_s1_ll_mem : rev76_s1_ll.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane11 rev76_vertex0 rev76_vertex1 rev76_s1_ll
    rev76_vertex0_mem rev76_vertex1_mem (by decide)
def rev76_s1_lr : FractionPoint := ⟨37488082241261273,48928332174000000,2025309014539974239493,5251412654459188000000⟩
theorem rev76_s1_lr_mem : rev76_s1_lr.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane11 rev76_vertex0 rev76_vertex1 rev76_s1_lr
    rev76_vertex0_mem rev76_vertex1_mem (by decide)
def rev76_s1_ul : FractionPoint := ⟨1935297561189487,2546743666000000,150679115621052151573,311718877974734000000⟩
theorem rev76_s1_ul_mem : rev76_s1_ul.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane33 rev76_vertex4 rev76_vertex3 rev76_s1_ul
    rev76_vertex4_mem rev76_vertex3_mem (by decide)
def rev76_s1_ur : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev76_s1_ur_mem : rev76_s1_ur.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane33 rev76_vertex4 rev76_vertex3 rev76_s1_ur
    rev76_vertex4_mem rev76_vertex3_mem (by decide)
theorem rev76_slab1 (p : Point) (hp : p∈IntegerCarrier rev76_planes)
    (hx0 : rev76_s1_ll.real.1≤p.1) (hx1 : p.1≤rev76_s1_lr.real.1) :
    p∈rationalHull (fractionRow76.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev76_plane11 rev76_plane33 rev76_s1_ll rev76_s1_lr rev76_s1_ul rev76_s1_ur
    (by decide) rev76_s1_ll_mem rev76_s1_lr_mem rev76_s1_ul_mem rev76_s1_ur_mem p
    (hp _ rev76_plane11_mem) (hp _ rev76_plane33_mem) hx0 hx1
def rev76_s2_ll : FractionPoint := ⟨37488082241261273,48928332174000000,2025309014539974239493,5251412654459188000000⟩
theorem rev76_s2_ll_mem : rev76_s2_ll.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane11 rev76_vertex0 rev76_vertex1 rev76_s2_ll
    rev76_vertex0_mem rev76_vertex1_mem (by decide)
def rev76_s2_lr : FractionPoint := ⟨20762435007382043,26840938933200000,5891497317622659060911,14404010938908892000000⟩
theorem rev76_s2_lr_mem : rev76_s2_lr.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane11 rev76_vertex0 rev76_vertex1 rev76_s2_lr
    rev76_vertex0_mem rev76_vertex1_mem (by decide)
def rev76_s2_ul : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev76_s2_ul_mem : rev76_s2_ul.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane74 rev76_vertex3 rev76_vertex2 rev76_s2_ul
    rev76_vertex3_mem rev76_vertex2_mem (by decide)
def rev76_s2_ur : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev76_s2_ur_mem : rev76_s2_ur.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane74 rev76_vertex3 rev76_vertex2 rev76_s2_ur
    rev76_vertex3_mem rev76_vertex2_mem (by decide)
theorem rev76_slab2 (p : Point) (hp : p∈IntegerCarrier rev76_planes)
    (hx0 : rev76_s2_ll.real.1≤p.1) (hx1 : p.1≤rev76_s2_lr.real.1) :
    p∈rationalHull (fractionRow76.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev76_plane11 rev76_plane74 rev76_s2_ll rev76_s2_lr rev76_s2_ul rev76_s2_ur
    (by decide) rev76_s2_ll_mem rev76_s2_lr_mem rev76_s2_ul_mem rev76_s2_ur_mem p
    (hp _ rev76_plane11_mem) (hp _ rev76_plane74_mem) hx0 hx1
def rev76_s3_ll : FractionPoint := ⟨20762435007382043,26840938933200000,5891497317622659060911,14404010938908892000000⟩
theorem rev76_s3_ll_mem : rev76_s3_ll.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane11 rev76_vertex0 rev76_vertex1 rev76_s3_ll
    rev76_vertex0_mem rev76_vertex1_mem (by decide)
def rev76_s3_lr : FractionPoint := ⟨57492125984335801,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev76_s3_lr_mem : rev76_s3_lr.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane11 rev76_vertex0 rev76_vertex1 rev76_s3_lr
    rev76_vertex0_mem rev76_vertex1_mem (by decide)
def rev76_s3_ul : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev76_s3_ul_mem : rev76_s3_ul.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane15 rev76_vertex2 rev76_vertex1 rev76_s3_ul
    rev76_vertex2_mem rev76_vertex1_mem (by decide)
def rev76_s3_ur : FractionPoint := ⟨57492125984335801,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev76_s3_ur_mem : rev76_s3_ur.real ∈ rationalHull (fractionRow76.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow76 rev76_plane15 rev76_vertex2 rev76_vertex1 rev76_s3_ur
    rev76_vertex2_mem rev76_vertex1_mem (by decide)
theorem rev76_slab3 (p : Point) (hp : p∈IntegerCarrier rev76_planes)
    (hx0 : rev76_s3_ll.real.1≤p.1) (hx1 : p.1≤rev76_s3_lr.real.1) :
    p∈rationalHull (fractionRow76.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev76_plane11 rev76_plane15 rev76_s3_ll rev76_s3_lr rev76_s3_ul rev76_s3_ur
    (by decide) rev76_s3_ll_mem rev76_s3_lr_mem rev76_s3_ul_mem rev76_s3_ur_mem p
    (hp _ rev76_plane11_mem) (hp _ rev76_plane15_mem) hx0 hx1
theorem rev76_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev76_planes) : rev76_s0_ll.real.1≤p.1 := by
  have hc := rev76_plane29.combine_sound rev76_plane33 1468788000000 699568000000 (by decide) (by decide) p
    (hp _ rev76_plane29_mem) (hp _ rev76_plane33_mem)
  exact (rev76_plane29.combine rev76_plane33 1468788000000 699568000000).xBoundCheck_sound rev76_s0_ll.nx rev76_s0_ll.dx true (by decide) p hc
theorem rev76_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev76_planes) : p.1≤rev76_s3_lr.real.1 := by
  have hc := rev76_plane11.combine_sound rev76_plane15 1468788000000 643972000000 (by decide) (by decide) p
    (hp _ rev76_plane11_mem) (hp _ rev76_plane15_mem)
  exact (rev76_plane11.combine rev76_plane15 1468788000000 643972000000).xBoundCheck_sound rev76_s3_lr.nx rev76_s3_lr.dx false (by decide) p hc
theorem rev76_hull (p : Point) (hp : p∈IntegerCarrier rev76_planes) :
    p∈rationalHull (fractionRow76.map FractionPoint.rational) := by
  have hxlo := rev76_bound0_lo p hp
  have hxhi := rev76_bound0_hi p hp
  by_cases h0 : p.1≤rev76_s0_lr.real.1
  · exact rev76_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev76_s1_lr.real.1
  · exact rev76_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev76_s2_lr.real.1
  · exact rev76_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev76_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull76 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,4,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow76 := by
  rw [← fractionRow76_correct]
  exact rev76_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull76
