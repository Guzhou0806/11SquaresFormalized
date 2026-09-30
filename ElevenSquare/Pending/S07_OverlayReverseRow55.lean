import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev55_planes : List IntegerPlane := integerOverlayPlanes ![5,2,6,4]
def rev55_plane29 : IntegerPlane := ⟨2099728000000,1393416000000,1359544139484⟩
theorem rev55_plane29_mem : rev55_plane29 ∈ rev55_planes := by decide
def rev55_plane51 : IntegerPlane := ⟨(-643972000000),(-2044968000000),(-726507475981)⟩
theorem rev55_plane51_mem : rev55_plane51 ∈ rev55_planes := by decide
def rev55_plane55 : IntegerPlane := ⟨1468788000000,(-2093220000000),256243273104⟩
theorem rev55_plane55_mem : rev55_plane55 ∈ rev55_planes := by decide
def rev55_plane69 : IntegerPlane := ⟨(-699568000000),2144520000000,259009891352⟩
theorem rev55_plane69_mem : rev55_plane69 ∈ rev55_planes := by decide
def rev55_plane73 : IntegerPlane := ⟨1468788000000,2093220000000,1212544726896⟩
theorem rev55_plane73_mem : rev55_plane73 ∈ rev55_planes := by decide
def rev55_vertex0 : FractionPoint := fractionRow55[0]!
theorem rev55_vertex0_mem : rev55_vertex0∈fractionRow55 := by decide
def rev55_vertex1 : FractionPoint := fractionRow55[1]!
theorem rev55_vertex1_mem : rev55_vertex1∈fractionRow55 := by decide
def rev55_vertex2 : FractionPoint := fractionRow55[2]!
theorem rev55_vertex2_mem : rev55_vertex2∈fractionRow55 := by decide
def rev55_vertex3 : FractionPoint := fractionRow55[3]!
theorem rev55_vertex3_mem : rev55_vertex3∈fractionRow55 := by decide
def rev55_vertex4 : FractionPoint := fractionRow55[4]!
theorem rev55_vertex4_mem : rev55_vertex4∈fractionRow55 := by decide
def rev55_s0_ll : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev55_s0_ll_mem : rev55_s0_ll.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane51 rev55_vertex3 rev55_vertex4 rev55_s0_ll
    rev55_vertex3_mem rev55_vertex4_mem (by decide)
def rev55_s0_lr : FractionPoint := ⟨3270661284241,7332499000000,1073633684195987089,4998241938344000000⟩
theorem rev55_s0_lr_mem : rev55_s0_lr.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane51 rev55_vertex3 rev55_vertex4 rev55_s0_lr
    rev55_vertex3_mem rev55_vertex4_mem (by decide)
def rev55_s0_ul : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev55_s0_ul_mem : rev55_s0_ul.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane69 rev55_vertex3 rev55_vertex2 rev55_s0_ul
    rev55_vertex3_mem rev55_vertex2_mem (by decide)
def rev55_s0_ur : FractionPoint := ⟨3270661284241,7332499000000,29287950748577,109987485000000⟩
theorem rev55_s0_ur_mem : rev55_s0_ur.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane69 rev55_vertex3 rev55_vertex2 rev55_s0_ur
    rev55_vertex3_mem rev55_vertex2_mem (by decide)
theorem rev55_slab0 (p : Point) (hp : p∈IntegerCarrier rev55_planes)
    (hx0 : rev55_s0_ll.real.1≤p.1) (hx1 : p.1≤rev55_s0_lr.real.1) :
    p∈rationalHull (fractionRow55.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev55_plane51 rev55_plane69 rev55_s0_ll rev55_s0_lr rev55_s0_ul rev55_s0_ur
    (by decide) rev55_s0_ll_mem rev55_s0_lr_mem rev55_s0_ul_mem rev55_s0_ur_mem p
    (hp _ rev55_plane51_mem) (hp _ rev55_plane69_mem) hx0 hx1
def rev55_s1_ll : FractionPoint := ⟨3270661284241,7332499000000,1073633684195987089,4998241938344000000⟩
theorem rev55_s1_ll_mem : rev55_s1_ll.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane51 rev55_vertex3 rev55_vertex4 rev55_s1_ll
    rev55_vertex3_mem rev55_vertex4_mem (by decide)
def rev55_s1_lr : FractionPoint := ⟨56798590905163597,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev55_s1_lr_mem : rev55_s1_lr.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane51 rev55_vertex3 rev55_vertex4 rev55_s1_lr
    rev55_vertex3_mem rev55_vertex4_mem (by decide)
def rev55_s1_ul : FractionPoint := ⟨3270661284241,7332499000000,29287950748577,109987485000000⟩
theorem rev55_s1_ul_mem : rev55_s1_ul.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane73 rev55_vertex2 rev55_vertex1 rev55_s1_ul
    rev55_vertex2_mem rev55_vertex1_mem (by decide)
def rev55_s1_ur : FractionPoint := ⟨56798590905163597,120877764684000000,5262050619012192035869,21085312882653540000000⟩
theorem rev55_s1_ur_mem : rev55_s1_ur.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane73 rev55_vertex2 rev55_vertex1 rev55_s1_ur
    rev55_vertex2_mem rev55_vertex1_mem (by decide)
theorem rev55_slab1 (p : Point) (hp : p∈IntegerCarrier rev55_planes)
    (hx0 : rev55_s1_ll.real.1≤p.1) (hx1 : p.1≤rev55_s1_lr.real.1) :
    p∈rationalHull (fractionRow55.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev55_plane51 rev55_plane73 rev55_s1_ll rev55_s1_lr rev55_s1_ul rev55_s1_ur
    (by decide) rev55_s1_ll_mem rev55_s1_lr_mem rev55_s1_ul_mem rev55_s1_ur_mem p
    (hp _ rev55_plane51_mem) (hp _ rev55_plane73_mem) hx0 hx1
def rev55_s2_ll : FractionPoint := ⟨56798590905163597,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev55_s2_ll_mem : rev55_s2_ll.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane55 rev55_vertex4 rev55_vertex0 rev55_s2_ll
    rev55_vertex4_mem rev55_vertex0_mem (by decide)
def rev55_s2_lr : FractionPoint := ⟨8029484447765151,16309444058000000,634535422927964715913,2844937874257230000000⟩
theorem rev55_s2_lr_mem : rev55_s2_lr.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane55 rev55_vertex4 rev55_vertex0 rev55_s2_lr
    rev55_vertex4_mem rev55_vertex0_mem (by decide)
def rev55_s2_ul : FractionPoint := ⟨56798590905163597,120877764684000000,5262050619012192035869,21085312882653540000000⟩
theorem rev55_s2_ul_mem : rev55_s2_ul.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane73 rev55_vertex2 rev55_vertex1 rev55_s2_ul
    rev55_vertex2_mem rev55_vertex1_mem (by decide)
def rev55_s2_ur : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev55_s2_ur_mem : rev55_s2_ur.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane73 rev55_vertex2 rev55_vertex1 rev55_s2_ur
    rev55_vertex2_mem rev55_vertex1_mem (by decide)
theorem rev55_slab2 (p : Point) (hp : p∈IntegerCarrier rev55_planes)
    (hx0 : rev55_s2_ll.real.1≤p.1) (hx1 : p.1≤rev55_s2_lr.real.1) :
    p∈rationalHull (fractionRow55.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev55_plane55 rev55_plane73 rev55_s2_ll rev55_s2_lr rev55_s2_ul rev55_s2_ur
    (by decide) rev55_s2_ll_mem rev55_s2_lr_mem rev55_s2_ul_mem rev55_s2_ur_mem p
    (hp _ rev55_plane55_mem) (hp _ rev55_plane73_mem) hx0 hx1
def rev55_s3_ll : FractionPoint := ⟨8029484447765151,16309444058000000,634535422927964715913,2844937874257230000000⟩
theorem rev55_s3_ll_mem : rev55_s3_ll.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane55 rev55_vertex4 rev55_vertex0 rev55_s3_ll
    rev55_vertex4_mem rev55_vertex0_mem (by decide)
def rev55_s3_lr : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev55_s3_lr_mem : rev55_s3_lr.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane55 rev55_vertex4 rev55_vertex0 rev55_s3_lr
    rev55_vertex4_mem rev55_vertex0_mem (by decide)
def rev55_s3_ul : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev55_s3_ul_mem : rev55_s3_ul.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane29 rev55_vertex1 rev55_vertex0 rev55_s3_ul
    rev55_vertex1_mem rev55_vertex0_mem (by decide)
def rev55_s3_ur : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev55_s3_ur_mem : rev55_s3_ur.real ∈ rationalHull (fractionRow55.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow55 rev55_plane29 rev55_vertex1 rev55_vertex0 rev55_s3_ur
    rev55_vertex1_mem rev55_vertex0_mem (by decide)
theorem rev55_slab3 (p : Point) (hp : p∈IntegerCarrier rev55_planes)
    (hx0 : rev55_s3_ll.real.1≤p.1) (hx1 : p.1≤rev55_s3_lr.real.1) :
    p∈rationalHull (fractionRow55.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev55_plane55 rev55_plane29 rev55_s3_ll rev55_s3_lr rev55_s3_ul rev55_s3_ur
    (by decide) rev55_s3_ll_mem rev55_s3_lr_mem rev55_s3_ul_mem rev55_s3_ur_mem p
    (hp _ rev55_plane55_mem) (hp _ rev55_plane29_mem) hx0 hx1
theorem rev55_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev55_planes) : rev55_s0_ll.real.1≤p.1 := by
  have hc := rev55_plane51.combine_sound rev55_plane69 2144520000000 2044968000000 (by decide) (by decide) p
    (hp _ rev55_plane51_mem) (hp _ rev55_plane69_mem)
  exact (rev55_plane51.combine rev55_plane69 2144520000000 2044968000000).xBoundCheck_sound rev55_s0_ll.nx rev55_s0_ll.dx true (by decide) p hc
theorem rev55_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev55_planes) : p.1≤rev55_s3_lr.real.1 := by
  have hc := rev55_plane29.combine_sound rev55_plane55 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev55_plane29_mem) (hp _ rev55_plane55_mem)
  exact (rev55_plane29.combine rev55_plane55 2093220000000 1393416000000).xBoundCheck_sound rev55_s3_lr.nx rev55_s3_lr.dx false (by decide) p hc
theorem rev55_hull (p : Point) (hp : p∈IntegerCarrier rev55_planes) :
    p∈rationalHull (fractionRow55.map FractionPoint.rational) := by
  have hxlo := rev55_bound0_lo p hp
  have hxhi := rev55_bound0_hi p hp
  by_cases h0 : p.1≤rev55_s0_lr.real.1
  · exact rev55_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev55_s1_lr.real.1
  · exact rev55_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev55_s2_lr.real.1
  · exact rev55_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev55_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull55 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,6,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow55 := by
  rw [← fractionRow55_correct]
  exact rev55_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull55
