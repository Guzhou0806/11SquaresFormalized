import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev56_planes : List IntegerPlane := integerOverlayPlanes ![5,2,6,5]
def rev56_plane30 : IntegerPlane := ⟨(-13084000000),2218132000000,610502975028⟩
theorem rev56_plane30_mem : rev56_plane30 ∈ rev56_planes := by decide
def rev56_plane46 : IntegerPlane := ⟨(-2218132000000),13084000000,(-610502975028)⟩
theorem rev56_plane46_mem : rev56_plane46 ∈ rev56_planes := by decide
def rev56_plane51 : IntegerPlane := ⟨(-643972000000),(-2044968000000),(-726507475981)⟩
theorem rev56_plane51_mem : rev56_plane51 ∈ rev56_planes := by decide
def rev56_plane68 : IntegerPlane := ⟨699568000000,(-2144520000000),(-259009891352)⟩
theorem rev56_plane68_mem : rev56_plane68 ∈ rev56_planes := by decide
def rev56_plane73 : IntegerPlane := ⟨2168356000000,(-51300000000),953534835544⟩
theorem rev56_plane73_mem : rev56_plane73 ∈ rev56_planes := by decide
def rev56_vertex0 : FractionPoint := fractionRow56[0]!
theorem rev56_vertex0_mem : rev56_vertex0∈fractionRow56 := by decide
def rev56_vertex1 : FractionPoint := fractionRow56[1]!
theorem rev56_vertex1_mem : rev56_vertex1∈fractionRow56 := by decide
def rev56_vertex2 : FractionPoint := fractionRow56[2]!
theorem rev56_vertex2_mem : rev56_vertex2∈fractionRow56 := by decide
def rev56_vertex3 : FractionPoint := fractionRow56[3]!
theorem rev56_vertex3_mem : rev56_vertex3∈fractionRow56 := by decide
def rev56_vertex4 : FractionPoint := fractionRow56[4]!
theorem rev56_vertex4_mem : rev56_vertex4∈fractionRow56 := by decide
def rev56_s0_ll : FractionPoint := ⟨314491167913198627,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev56_s0_ll_mem : rev56_s0_ll.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane51 rev56_vertex2 rev56_vertex3 rev56_s0_ll
    rev56_vertex2_mem rev56_vertex3_mem (by decide)
def rev56_s0_lr : FractionPoint := ⟨50875247919,183754000000,50368209794259203,187885524936000000⟩
theorem rev56_s0_lr_mem : rev56_s0_lr.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane51 rev56_vertex2 rev56_vertex3 rev56_s0_lr
    rev56_vertex2_mem rev56_vertex3_mem (by decide)
def rev56_s0_ul : FractionPoint := ⟨314491167913198627,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev56_s0_ul_mem : rev56_s0_ul.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane46 rev56_vertex2 rev56_vertex1 rev56_s0_ul
    rev56_vertex2_mem rev56_vertex1_mem (by decide)
def rev56_s0_ur : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev56_s0_ur_mem : rev56_s0_ur.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane46 rev56_vertex2 rev56_vertex1 rev56_s0_ur
    rev56_vertex2_mem rev56_vertex1_mem (by decide)
theorem rev56_slab0 (p : Point) (hp : p∈IntegerCarrier rev56_planes)
    (hx0 : rev56_s0_ll.real.1≤p.1) (hx1 : p.1≤rev56_s0_lr.real.1) :
    p∈rationalHull (fractionRow56.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev56_plane51 rev56_plane46 rev56_s0_ll rev56_s0_lr rev56_s0_ul rev56_s0_ur
    (by decide) rev56_s0_ll_mem rev56_s0_lr_mem rev56_s0_ul_mem rev56_s0_ur_mem p
    (hp _ rev56_plane51_mem) (hp _ rev56_plane46_mem) hx0 hx1
def rev56_s1_ll : FractionPoint := ⟨50875247919,183754000000,50368209794259203,187885524936000000⟩
theorem rev56_s1_ll_mem : rev56_s1_ll.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane51 rev56_vertex2 rev56_vertex3 rev56_s1_ll
    rev56_vertex2_mem rev56_vertex3_mem (by decide)
def rev56_s1_lr : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev56_s1_lr_mem : rev56_s1_lr.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane51 rev56_vertex2 rev56_vertex3 rev56_s1_lr
    rev56_vertex2_mem rev56_vertex3_mem (by decide)
def rev56_s1_ul : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev56_s1_ul_mem : rev56_s1_ul.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane30 rev56_vertex1 rev56_vertex0 rev56_s1_ul
    rev56_vertex1_mem rev56_vertex0_mem (by decide)
def rev56_s1_ur : FractionPoint := ⟨1862939987124017,5093487332000000,783490969061240245931,2824506810675956000000⟩
theorem rev56_s1_ur_mem : rev56_s1_ur.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane30 rev56_vertex1 rev56_vertex0 rev56_s1_ur
    rev56_vertex1_mem rev56_vertex0_mem (by decide)
theorem rev56_slab1 (p : Point) (hp : p∈IntegerCarrier rev56_planes)
    (hx0 : rev56_s1_ll.real.1≤p.1) (hx1 : p.1≤rev56_s1_lr.real.1) :
    p∈rationalHull (fractionRow56.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev56_plane51 rev56_plane30 rev56_s1_ll rev56_s1_lr rev56_s1_ul rev56_s1_ur
    (by decide) rev56_s1_ll_mem rev56_s1_lr_mem rev56_s1_ul_mem rev56_s1_ur_mem p
    (hp _ rev56_plane51_mem) (hp _ rev56_plane30_mem) hx0 hx1
def rev56_s2_ll : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev56_s2_ll_mem : rev56_s2_ll.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane68 rev56_vertex3 rev56_vertex4 rev56_s2_ll
    rev56_vertex3_mem rev56_vertex4_mem (by decide)
def rev56_s2_lr : FractionPoint := ⟨3270661284241,7332499000000,29287950748577,109987485000000⟩
theorem rev56_s2_lr_mem : rev56_s2_lr.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane68 rev56_vertex3 rev56_vertex4 rev56_s2_lr
    rev56_vertex3_mem rev56_vertex4_mem (by decide)
def rev56_s2_ul : FractionPoint := ⟨1862939987124017,5093487332000000,783490969061240245931,2824506810675956000000⟩
theorem rev56_s2_ul_mem : rev56_s2_ul.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane30 rev56_vertex1 rev56_vertex0 rev56_s2_ul
    rev56_vertex1_mem rev56_vertex0_mem (by decide)
def rev56_s2_ur : FractionPoint := ⟨3270661284241,7332499000000,564913223266605527,2033056333983500000⟩
theorem rev56_s2_ur_mem : rev56_s2_ur.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane30 rev56_vertex1 rev56_vertex0 rev56_s2_ur
    rev56_vertex1_mem rev56_vertex0_mem (by decide)
theorem rev56_slab2 (p : Point) (hp : p∈IntegerCarrier rev56_planes)
    (hx0 : rev56_s2_ll.real.1≤p.1) (hx1 : p.1≤rev56_s2_lr.real.1) :
    p∈rationalHull (fractionRow56.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev56_plane68 rev56_plane30 rev56_s2_ll rev56_s2_lr rev56_s2_ul rev56_s2_ur
    (by decide) rev56_s2_ll_mem rev56_s2_lr_mem rev56_s2_ul_mem rev56_s2_ur_mem p
    (hp _ rev56_plane68_mem) (hp _ rev56_plane30_mem) hx0 hx1
def rev56_s3_ll : FractionPoint := ⟨3270661284241,7332499000000,29287950748577,109987485000000⟩
theorem rev56_s3_ll_mem : rev56_s3_ll.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane73 rev56_vertex4 rev56_vertex0 rev56_s3_ll
    rev56_vertex4_mem rev56_vertex0_mem (by decide)
def rev56_s3_lr : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev56_s3_lr_mem : rev56_s3_lr.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane73 rev56_vertex4 rev56_vertex0 rev56_s3_lr
    rev56_vertex4_mem rev56_vertex0_mem (by decide)
def rev56_s3_ul : FractionPoint := ⟨3270661284241,7332499000000,564913223266605527,2033056333983500000⟩
theorem rev56_s3_ul_mem : rev56_s3_ul.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane30 rev56_vertex1 rev56_vertex0 rev56_s3_ul
    rev56_vertex1_mem rev56_vertex0_mem (by decide)
def rev56_s3_ur : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev56_s3_ur_mem : rev56_s3_ur.real ∈ rationalHull (fractionRow56.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow56 rev56_plane30 rev56_vertex1 rev56_vertex0 rev56_s3_ur
    rev56_vertex1_mem rev56_vertex0_mem (by decide)
theorem rev56_slab3 (p : Point) (hp : p∈IntegerCarrier rev56_planes)
    (hx0 : rev56_s3_ll.real.1≤p.1) (hx1 : p.1≤rev56_s3_lr.real.1) :
    p∈rationalHull (fractionRow56.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev56_plane73 rev56_plane30 rev56_s3_ll rev56_s3_lr rev56_s3_ul rev56_s3_ur
    (by decide) rev56_s3_ll_mem rev56_s3_lr_mem rev56_s3_ul_mem rev56_s3_ur_mem p
    (hp _ rev56_plane73_mem) (hp _ rev56_plane30_mem) hx0 hx1
theorem rev56_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev56_planes) : rev56_s0_ll.real.1≤p.1 := by
  have hc := rev56_plane46.combine_sound rev56_plane51 2044968000000 13084000000 (by decide) (by decide) p
    (hp _ rev56_plane46_mem) (hp _ rev56_plane51_mem)
  exact (rev56_plane46.combine rev56_plane51 2044968000000 13084000000).xBoundCheck_sound rev56_s0_ll.nx rev56_s0_ll.dx true (by decide) p hc
theorem rev56_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev56_planes) : p.1≤rev56_s3_lr.real.1 := by
  have hc := rev56_plane30.combine_sound rev56_plane73 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev56_plane30_mem) (hp _ rev56_plane73_mem)
  exact (rev56_plane30.combine rev56_plane73 51300000000 2218132000000).xBoundCheck_sound rev56_s3_lr.nx rev56_s3_lr.dx false (by decide) p hc
theorem rev56_hull (p : Point) (hp : p∈IntegerCarrier rev56_planes) :
    p∈rationalHull (fractionRow56.map FractionPoint.rational) := by
  have hxlo := rev56_bound0_lo p hp
  have hxhi := rev56_bound0_hi p hp
  by_cases h0 : p.1≤rev56_s0_lr.real.1
  · exact rev56_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev56_s1_lr.real.1
  · exact rev56_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev56_s2_lr.real.1
  · exact rev56_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev56_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull56 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,6,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow56 := by
  rw [← fractionRow56_correct]
  exact rev56_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull56
