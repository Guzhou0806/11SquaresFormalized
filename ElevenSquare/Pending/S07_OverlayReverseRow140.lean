import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev140_planes : List IntegerPlane := integerOverlayPlanes ![9,10,5,2]
def rev140_plane12 : IntegerPlane := ⟨(-2044968000000),643972000000,(-82535475981)⟩
theorem rev140_plane12_mem : rev140_plane12 ∈ rev140_planes := by decide
def rev140_plane17 : IntegerPlane := ⟨13084000000,2218132000000,1607629024972⟩
theorem rev140_plane17_mem : rev140_plane17 ∈ rev140_planes := by decide
def rev140_plane30 : IntegerPlane := ⟨(-51300000000),(-2168356000000),(-1214821164456)⟩
theorem rev140_plane30_mem : rev140_plane30 ∈ rev140_planes := by decide
def rev140_plane35 : IntegerPlane := ⟨(-2144520000000),(-699568000000),(-958577891352)⟩
theorem rev140_plane35_mem : rev140_plane35 ∈ rev140_planes := by decide
def rev140_plane70 : IntegerPlane := ⟨2218132000000,13084000000,623586975028⟩
theorem rev140_plane70_mem : rev140_plane70 ∈ rev140_planes := by decide
def rev140_vertex0 : FractionPoint := fractionRow140[0]!
theorem rev140_vertex0_mem : rev140_vertex0∈fractionRow140 := by decide
def rev140_vertex1 : FractionPoint := fractionRow140[1]!
theorem rev140_vertex1_mem : rev140_vertex1∈fractionRow140 := by decide
def rev140_vertex2 : FractionPoint := fractionRow140[2]!
theorem rev140_vertex2_mem : rev140_vertex2∈fractionRow140 := by decide
def rev140_vertex3 : FractionPoint := fractionRow140[3]!
theorem rev140_vertex3_mem : rev140_vertex3∈fractionRow140 := by decide
def rev140_vertex4 : FractionPoint := fractionRow140[4]!
theorem rev140_vertex4_mem : rev140_vertex4∈fractionRow140 := by decide
def rev140_s0_ll : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev140_s0_ll_mem : rev140_s0_ll.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane35 rev140_vertex1 rev140_vertex2 rev140_s0_ll
    rev140_vertex1_mem rev140_vertex2_mem (by decide)
def rev140_s0_lr : FractionPoint := ⟨29287950748577,109987485000000,4061837715759,7332499000000⟩
theorem rev140_s0_lr_mem : rev140_s0_lr.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane35 rev140_vertex1 rev140_vertex2 rev140_s0_lr
    rev140_vertex1_mem rev140_vertex2_mem (by decide)
def rev140_s0_ul : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev140_s0_ul_mem : rev140_s0_ul.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane12 rev140_vertex1 rev140_vertex0 rev140_s0_ul
    rev140_vertex1_mem rev140_vertex0_mem (by decide)
def rev140_s0_ur : FractionPoint := ⟨29287950748577,109987485000000,16938350879995970917,23609620230140000000⟩
theorem rev140_s0_ur_mem : rev140_s0_ur.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane12 rev140_vertex1 rev140_vertex0 rev140_s0_ur
    rev140_vertex1_mem rev140_vertex0_mem (by decide)
theorem rev140_slab0 (p : Point) (hp : p∈IntegerCarrier rev140_planes)
    (hx0 : rev140_s0_ll.real.1≤p.1) (hx1 : p.1≤rev140_s0_lr.real.1) :
    p∈rationalHull (fractionRow140.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev140_plane35 rev140_plane12 rev140_s0_ll rev140_s0_lr rev140_s0_ul rev140_s0_ur
    (by decide) rev140_s0_ll_mem rev140_s0_lr_mem rev140_s0_ul_mem rev140_s0_ur_mem p
    (hp _ rev140_plane35_mem) (hp _ rev140_plane12_mem) hx0 hx1
def rev140_s1_ll : FractionPoint := ⟨29287950748577,109987485000000,4061837715759,7332499000000⟩
theorem rev140_s1_ll_mem : rev140_s1_ll.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane30 rev140_vertex2 rev140_vertex3 rev140_s1_ll
    rev140_vertex2_mem rev140_vertex3_mem (by decide)
def rev140_s1_lr : FractionPoint := ⟨43512237817069867,162301238908000000,2564931608458583285223,4630616647284148000000⟩
theorem rev140_s1_lr_mem : rev140_s1_lr.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane30 rev140_vertex2 rev140_vertex3 rev140_s1_lr
    rev140_vertex2_mem rev140_vertex3_mem (by decide)
def rev140_s1_ul : FractionPoint := ⟨29287950748577,109987485000000,16938350879995970917,23609620230140000000⟩
theorem rev140_s1_ul_mem : rev140_s1_ul.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane12 rev140_vertex1 rev140_vertex0 rev140_s1_ul
    rev140_vertex1_mem rev140_vertex0_mem (by decide)
def rev140_s1_ur : FractionPoint := ⟨43512237817069867,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev140_s1_ur_mem : rev140_s1_ur.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane12 rev140_vertex1 rev140_vertex0 rev140_s1_ur
    rev140_vertex1_mem rev140_vertex0_mem (by decide)
theorem rev140_slab1 (p : Point) (hp : p∈IntegerCarrier rev140_planes)
    (hx0 : rev140_s1_ll.real.1≤p.1) (hx1 : p.1≤rev140_s1_lr.real.1) :
    p∈rationalHull (fractionRow140.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev140_plane30 rev140_plane12 rev140_s1_ll rev140_s1_lr rev140_s1_ul rev140_s1_ur
    (by decide) rev140_s1_ll_mem rev140_s1_lr_mem rev140_s1_ul_mem rev140_s1_ur_mem p
    (hp _ rev140_plane30_mem) (hp _ rev140_plane12_mem) hx0 hx1
def rev140_s2_ll : FractionPoint := ⟨43512237817069867,162301238908000000,2564931608458583285223,4630616647284148000000⟩
theorem rev140_s2_ll_mem : rev140_s2_ll.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane30 rev140_vertex2 rev140_vertex3 rev140_s2_ll
    rev140_vertex2_mem rev140_vertex3_mem (by decide)
def rev140_s2_lr : FractionPoint := ⟨50875247919,183754000000,2902873000463199,5242685374000000⟩
theorem rev140_s2_lr_mem : rev140_s2_lr.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane30 rev140_vertex2 rev140_vertex3 rev140_s2_lr
    rev140_vertex2_mem rev140_vertex3_mem (by decide)
def rev140_s2_ul : FractionPoint := ⟨43512237817069867,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev140_s2_ul_mem : rev140_s2_ul.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane17 rev140_vertex0 rev140_vertex4 rev140_s2_ul
    rev140_vertex0_mem rev140_vertex4_mem (by decide)
def rev140_s2_ur : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev140_s2_ur_mem : rev140_s2_ur.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane17 rev140_vertex0 rev140_vertex4 rev140_s2_ur
    rev140_vertex0_mem rev140_vertex4_mem (by decide)
theorem rev140_slab2 (p : Point) (hp : p∈IntegerCarrier rev140_planes)
    (hx0 : rev140_s2_ll.real.1≤p.1) (hx1 : p.1≤rev140_s2_lr.real.1) :
    p∈rationalHull (fractionRow140.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev140_plane30 rev140_plane17 rev140_s2_ll rev140_s2_lr rev140_s2_ul rev140_s2_ur
    (by decide) rev140_s2_ll_mem rev140_s2_lr_mem rev140_s2_ul_mem rev140_s2_ur_mem p
    (hp _ rev140_plane30_mem) (hp _ rev140_plane17_mem) hx0 hx1
def rev140_s3_ll : FractionPoint := ⟨50875247919,183754000000,2902873000463199,5242685374000000⟩
theorem rev140_s3_ll_mem : rev140_s3_ll.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane30 rev140_vertex2 rev140_vertex3 rev140_s3_ll
    rev140_vertex2_mem rev140_vertex3_mem (by decide)
def rev140_s3_lr : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev140_s3_lr_mem : rev140_s3_lr.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane30 rev140_vertex2 rev140_vertex3 rev140_s3_lr
    rev140_vertex2_mem rev140_vertex3_mem (by decide)
def rev140_s3_ul : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev140_s3_ul_mem : rev140_s3_ul.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane70 rev140_vertex4 rev140_vertex3 rev140_s3_ul
    rev140_vertex4_mem rev140_vertex3_mem (by decide)
def rev140_s3_ur : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev140_s3_ur_mem : rev140_s3_ur.real ∈ rationalHull (fractionRow140.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow140 rev140_plane70 rev140_vertex4 rev140_vertex3 rev140_s3_ur
    rev140_vertex4_mem rev140_vertex3_mem (by decide)
theorem rev140_slab3 (p : Point) (hp : p∈IntegerCarrier rev140_planes)
    (hx0 : rev140_s3_ll.real.1≤p.1) (hx1 : p.1≤rev140_s3_lr.real.1) :
    p∈rationalHull (fractionRow140.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev140_plane30 rev140_plane70 rev140_s3_ll rev140_s3_lr rev140_s3_ul rev140_s3_ur
    (by decide) rev140_s3_ll_mem rev140_s3_lr_mem rev140_s3_ul_mem rev140_s3_ur_mem p
    (hp _ rev140_plane30_mem) (hp _ rev140_plane70_mem) hx0 hx1
theorem rev140_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev140_planes) : rev140_s0_ll.real.1≤p.1 := by
  have hc := rev140_plane12.combine_sound rev140_plane35 699568000000 643972000000 (by decide) (by decide) p
    (hp _ rev140_plane12_mem) (hp _ rev140_plane35_mem)
  exact (rev140_plane12.combine rev140_plane35 699568000000 643972000000).xBoundCheck_sound rev140_s0_ll.nx rev140_s0_ll.dx true (by decide) p hc
theorem rev140_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev140_planes) : p.1≤rev140_s3_lr.real.1 := by
  have hc := rev140_plane30.combine_sound rev140_plane70 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev140_plane30_mem) (hp _ rev140_plane70_mem)
  exact (rev140_plane30.combine rev140_plane70 13084000000 2168356000000).xBoundCheck_sound rev140_s3_lr.nx rev140_s3_lr.dx false (by decide) p hc
theorem rev140_hull (p : Point) (hp : p∈IntegerCarrier rev140_planes) :
    p∈rationalHull (fractionRow140.map FractionPoint.rational) := by
  have hxlo := rev140_bound0_lo p hp
  have hxhi := rev140_bound0_hi p hp
  by_cases h0 : p.1≤rev140_s0_lr.real.1
  · exact rev140_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev140_s1_lr.real.1
  · exact rev140_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev140_s2_lr.real.1
  · exact rev140_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev140_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull140 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,10,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow140 := by
  rw [← fractionRow140_correct]
  exact rev140_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull140
