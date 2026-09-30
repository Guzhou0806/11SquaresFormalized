import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev187_planes : List IntegerPlane := integerOverlayPlanes ![13,10,4,6]
def rev187_plane14 : IntegerPlane := ⟨2099728000000,(-1393416000000),(-33871860516)⟩
theorem rev187_plane14_mem : rev187_plane14 ∈ rev187_planes := by decide
def rev187_plane49 : IntegerPlane := ⟨(-699568000000),(-2144520000000),(-1885510108648)⟩
theorem rev187_plane49_mem : rev187_plane49 ∈ rev187_planes := by decide
def rev187_plane53 : IntegerPlane := ⟨1468788000000,(-2093220000000),(-880675273104)⟩
theorem rev187_plane53_mem : rev187_plane53 ∈ rev187_planes := by decide
def rev187_plane71 : IntegerPlane := ⟨(-643972000000),2044968000000,1318460524019⟩
theorem rev187_plane71_mem : rev187_plane71 ∈ rev187_planes := by decide
def rev187_plane75 : IntegerPlane := ⟨1468788000000,2093220000000,2349463273104⟩
theorem rev187_plane75_mem : rev187_plane75 ∈ rev187_planes := by decide
def rev187_vertex0 : FractionPoint := fractionRow187[0]!
theorem rev187_vertex0_mem : rev187_vertex0∈fractionRow187 := by decide
def rev187_vertex1 : FractionPoint := fractionRow187[1]!
theorem rev187_vertex1_mem : rev187_vertex1∈fractionRow187 := by decide
def rev187_vertex2 : FractionPoint := fractionRow187[2]!
theorem rev187_vertex2_mem : rev187_vertex2∈fractionRow187 := by decide
def rev187_vertex3 : FractionPoint := fractionRow187[3]!
theorem rev187_vertex3_mem : rev187_vertex3∈fractionRow187 := by decide
def rev187_vertex4 : FractionPoint := fractionRow187[4]!
theorem rev187_vertex4_mem : rev187_vertex4∈fractionRow187 := by decide
def rev187_s0_ll : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev187_s0_ll_mem : rev187_s0_ll.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane49 rev187_vertex0 rev187_vertex1 rev187_s0_ll
    rev187_vertex0_mem rev187_vertex1_mem (by decide)
def rev187_s0_lr : FractionPoint := ⟨3270661284241,7332499000000,80699534251423,109987485000000⟩
theorem rev187_s0_lr_mem : rev187_s0_lr.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane49 rev187_vertex0 rev187_vertex1 rev187_s0_lr
    rev187_vertex0_mem rev187_vertex1_mem (by decide)
def rev187_s0_ul : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev187_s0_ul_mem : rev187_s0_ul.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane71 rev187_vertex0 rev187_vertex4 rev187_s0_ul
    rev187_vertex0_mem rev187_vertex4_mem (by decide)
def rev187_s0_ur : FractionPoint := ⟨3270661284241,7332499000000,3924608254148012911,4998241938344000000⟩
theorem rev187_s0_ur_mem : rev187_s0_ur.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane71 rev187_vertex0 rev187_vertex4 rev187_s0_ur
    rev187_vertex0_mem rev187_vertex4_mem (by decide)
theorem rev187_slab0 (p : Point) (hp : p∈IntegerCarrier rev187_planes)
    (hx0 : rev187_s0_ll.real.1≤p.1) (hx1 : p.1≤rev187_s0_lr.real.1) :
    p∈rationalHull (fractionRow187.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev187_plane49 rev187_plane71 rev187_s0_ll rev187_s0_lr rev187_s0_ul rev187_s0_ur
    (by decide) rev187_s0_ll_mem rev187_s0_lr_mem rev187_s0_ul_mem rev187_s0_ur_mem p
    (hp _ rev187_plane49_mem) (hp _ rev187_plane71_mem) hx0 hx1
def rev187_s1_ll : FractionPoint := ⟨3270661284241,7332499000000,80699534251423,109987485000000⟩
theorem rev187_s1_ll_mem : rev187_s1_ll.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane53 rev187_vertex1 rev187_vertex2 rev187_s1_ll
    rev187_vertex1_mem rev187_vertex2_mem (by decide)
def rev187_s1_lr : FractionPoint := ⟨56798590905163597,120877764684000000,15823262263641347964131,21085312882653540000000⟩
theorem rev187_s1_lr_mem : rev187_s1_lr.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane53 rev187_vertex1 rev187_vertex2 rev187_s1_lr
    rev187_vertex1_mem rev187_vertex2_mem (by decide)
def rev187_s1_ul : FractionPoint := ⟨3270661284241,7332499000000,3924608254148012911,4998241938344000000⟩
theorem rev187_s1_ul_mem : rev187_s1_ul.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane71 rev187_vertex0 rev187_vertex4 rev187_s1_ul
    rev187_vertex0_mem rev187_vertex4_mem (by decide)
def rev187_s1_ur : FractionPoint := ⟨56798590905163597,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev187_s1_ur_mem : rev187_s1_ur.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane71 rev187_vertex0 rev187_vertex4 rev187_s1_ur
    rev187_vertex0_mem rev187_vertex4_mem (by decide)
theorem rev187_slab1 (p : Point) (hp : p∈IntegerCarrier rev187_planes)
    (hx0 : rev187_s1_ll.real.1≤p.1) (hx1 : p.1≤rev187_s1_lr.real.1) :
    p∈rationalHull (fractionRow187.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev187_plane53 rev187_plane71 rev187_s1_ll rev187_s1_lr rev187_s1_ul rev187_s1_ur
    (by decide) rev187_s1_ll_mem rev187_s1_lr_mem rev187_s1_ul_mem rev187_s1_ur_mem p
    (hp _ rev187_plane53_mem) (hp _ rev187_plane71_mem) hx0 hx1
def rev187_s2_ll : FractionPoint := ⟨56798590905163597,120877764684000000,15823262263641347964131,21085312882653540000000⟩
theorem rev187_s2_ll_mem : rev187_s2_ll.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane53 rev187_vertex1 rev187_vertex2 rev187_s2_ll
    rev187_vertex1_mem rev187_vertex2_mem (by decide)
def rev187_s2_lr : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev187_s2_lr_mem : rev187_s2_lr.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane53 rev187_vertex1 rev187_vertex2 rev187_s2_lr
    rev187_vertex1_mem rev187_vertex2_mem (by decide)
def rev187_s2_ul : FractionPoint := ⟨56798590905163597,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev187_s2_ul_mem : rev187_s2_ul.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane75 rev187_vertex4 rev187_vertex3 rev187_s2_ul
    rev187_vertex4_mem rev187_vertex3_mem (by decide)
def rev187_s2_ur : FractionPoint := ⟨8029484447765151,16309444058000000,2210402451329265284087,2844937874257230000000⟩
theorem rev187_s2_ur_mem : rev187_s2_ur.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane75 rev187_vertex4 rev187_vertex3 rev187_s2_ur
    rev187_vertex4_mem rev187_vertex3_mem (by decide)
theorem rev187_slab2 (p : Point) (hp : p∈IntegerCarrier rev187_planes)
    (hx0 : rev187_s2_ll.real.1≤p.1) (hx1 : p.1≤rev187_s2_lr.real.1) :
    p∈rationalHull (fractionRow187.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev187_plane53 rev187_plane75 rev187_s2_ll rev187_s2_lr rev187_s2_ul rev187_s2_ur
    (by decide) rev187_s2_ll_mem rev187_s2_lr_mem rev187_s2_ul_mem rev187_s2_ur_mem p
    (hp _ rev187_plane53_mem) (hp _ rev187_plane75_mem) hx0 hx1
def rev187_s3_ll : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev187_s3_ll_mem : rev187_s3_ll.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane14 rev187_vertex2 rev187_vertex3 rev187_s3_ll
    rev187_vertex2_mem rev187_vertex3_mem (by decide)
def rev187_s3_lr : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev187_s3_lr_mem : rev187_s3_lr.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane14 rev187_vertex2 rev187_vertex3 rev187_s3_lr
    rev187_vertex2_mem rev187_vertex3_mem (by decide)
def rev187_s3_ul : FractionPoint := ⟨8029484447765151,16309444058000000,2210402451329265284087,2844937874257230000000⟩
theorem rev187_s3_ul_mem : rev187_s3_ul.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane75 rev187_vertex4 rev187_vertex3 rev187_s3_ul
    rev187_vertex4_mem rev187_vertex3_mem (by decide)
def rev187_s3_ur : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev187_s3_ur_mem : rev187_s3_ur.real ∈ rationalHull (fractionRow187.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow187 rev187_plane75 rev187_vertex4 rev187_vertex3 rev187_s3_ur
    rev187_vertex4_mem rev187_vertex3_mem (by decide)
theorem rev187_slab3 (p : Point) (hp : p∈IntegerCarrier rev187_planes)
    (hx0 : rev187_s3_ll.real.1≤p.1) (hx1 : p.1≤rev187_s3_lr.real.1) :
    p∈rationalHull (fractionRow187.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev187_plane14 rev187_plane75 rev187_s3_ll rev187_s3_lr rev187_s3_ul rev187_s3_ur
    (by decide) rev187_s3_ll_mem rev187_s3_lr_mem rev187_s3_ul_mem rev187_s3_ur_mem p
    (hp _ rev187_plane14_mem) (hp _ rev187_plane75_mem) hx0 hx1
theorem rev187_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev187_planes) : rev187_s0_ll.real.1≤p.1 := by
  have hc := rev187_plane49.combine_sound rev187_plane71 2044968000000 2144520000000 (by decide) (by decide) p
    (hp _ rev187_plane49_mem) (hp _ rev187_plane71_mem)
  exact (rev187_plane49.combine rev187_plane71 2044968000000 2144520000000).xBoundCheck_sound rev187_s0_ll.nx rev187_s0_ll.dx true (by decide) p hc
theorem rev187_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev187_planes) : p.1≤rev187_s3_lr.real.1 := by
  have hc := rev187_plane14.combine_sound rev187_plane75 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev187_plane14_mem) (hp _ rev187_plane75_mem)
  exact (rev187_plane14.combine rev187_plane75 2093220000000 1393416000000).xBoundCheck_sound rev187_s3_lr.nx rev187_s3_lr.dx false (by decide) p hc
theorem rev187_hull (p : Point) (hp : p∈IntegerCarrier rev187_planes) :
    p∈rationalHull (fractionRow187.map FractionPoint.rational) := by
  have hxlo := rev187_bound0_lo p hp
  have hxhi := rev187_bound0_hi p hp
  by_cases h0 : p.1≤rev187_s0_lr.real.1
  · exact rev187_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev187_s1_lr.real.1
  · exact rev187_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev187_s2_lr.real.1
  · exact rev187_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev187_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull187 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,4,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow187 := by
  rw [← fractionRow187_correct]
  exact rev187_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull187
