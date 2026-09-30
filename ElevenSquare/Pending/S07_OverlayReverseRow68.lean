import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev68_planes : List IntegerPlane := integerOverlayPlanes ![5,6,2,5]
def rev68_plane8 : IntegerPlane := ⟨(-2144520000000),699568000000,(-259009891352)⟩
theorem rev68_plane8_mem : rev68_plane8 ∈ rev68_planes := by decide
def rev68_plane13 : IntegerPlane := ⟨(-51300000000),2168356000000,953534835544⟩
theorem rev68_plane13_mem : rev68_plane13 ∈ rev68_planes := by decide
def rev68_plane26 : IntegerPlane := ⟨13084000000,(-2218132000000),(-610502975028)⟩
theorem rev68_plane26_mem : rev68_plane26 ∈ rev68_planes := by decide
def rev68_plane31 : IntegerPlane := ⟨(-2044968000000),(-643972000000),(-726507475981)⟩
theorem rev68_plane31_mem : rev68_plane31 ∈ rev68_planes := by decide
def rev68_plane50 : IntegerPlane := ⟨2218132000000,(-13084000000),610502975028⟩
theorem rev68_plane50_mem : rev68_plane50 ∈ rev68_planes := by decide
def rev68_vertex0 : FractionPoint := fractionRow68[0]!
theorem rev68_vertex0_mem : rev68_vertex0∈fractionRow68 := by decide
def rev68_vertex1 : FractionPoint := fractionRow68[1]!
theorem rev68_vertex1_mem : rev68_vertex1∈fractionRow68 := by decide
def rev68_vertex2 : FractionPoint := fractionRow68[2]!
theorem rev68_vertex2_mem : rev68_vertex2∈fractionRow68 := by decide
def rev68_vertex3 : FractionPoint := fractionRow68[3]!
theorem rev68_vertex3_mem : rev68_vertex3∈fractionRow68 := by decide
def rev68_vertex4 : FractionPoint := fractionRow68[4]!
theorem rev68_vertex4_mem : rev68_vertex4∈fractionRow68 := by decide
def rev68_s0_ll : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev68_s0_ll_mem : rev68_s0_ll.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane31 rev68_vertex1 rev68_vertex2 rev68_s0_ll
    rev68_vertex1_mem rev68_vertex2_mem (by decide)
def rev68_s0_lr : FractionPoint := ⟨29287950748577,109987485000000,6671269350144029083,23609620230140000000⟩
theorem rev68_s0_lr_mem : rev68_s0_lr.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane31 rev68_vertex1 rev68_vertex2 rev68_s0_lr
    rev68_vertex1_mem rev68_vertex2_mem (by decide)
def rev68_s0_ul : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev68_s0_ul_mem : rev68_s0_ul.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane8 rev68_vertex1 rev68_vertex0 rev68_s0_ul
    rev68_vertex1_mem rev68_vertex0_mem (by decide)
def rev68_s0_ur : FractionPoint := ⟨29287950748577,109987485000000,3270661284241,7332499000000⟩
theorem rev68_s0_ur_mem : rev68_s0_ur.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane8 rev68_vertex1 rev68_vertex0 rev68_s0_ur
    rev68_vertex1_mem rev68_vertex0_mem (by decide)
theorem rev68_slab0 (p : Point) (hp : p∈IntegerCarrier rev68_planes)
    (hx0 : rev68_s0_ll.real.1≤p.1) (hx1 : p.1≤rev68_s0_lr.real.1) :
    p∈rationalHull (fractionRow68.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev68_plane31 rev68_plane8 rev68_s0_ll rev68_s0_lr rev68_s0_ul rev68_s0_ur
    (by decide) rev68_s0_ll_mem rev68_s0_lr_mem rev68_s0_ul_mem rev68_s0_ur_mem p
    (hp _ rev68_plane31_mem) (hp _ rev68_plane8_mem) hx0 hx1
def rev68_s1_ll : FractionPoint := ⟨29287950748577,109987485000000,6671269350144029083,23609620230140000000⟩
theorem rev68_s1_ll_mem : rev68_s1_ll.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane31 rev68_vertex1 rev68_vertex2 rev68_s1_ll
    rev68_vertex1_mem rev68_vertex2_mem (by decide)
def rev68_s1_lr : FractionPoint := ⟨43512237817069867,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev68_s1_lr_mem : rev68_s1_lr.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane31 rev68_vertex1 rev68_vertex2 rev68_s1_lr
    rev68_vertex1_mem rev68_vertex2_mem (by decide)
def rev68_s1_ul : FractionPoint := ⟨29287950748577,109987485000000,3270661284241,7332499000000⟩
theorem rev68_s1_ul_mem : rev68_s1_ul.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane13 rev68_vertex0 rev68_vertex4 rev68_s1_ul
    rev68_vertex0_mem rev68_vertex4_mem (by decide)
def rev68_s1_ur : FractionPoint := ⟨43512237817069867,162301238908000000,2065685038825564714777,4630616647284148000000⟩
theorem rev68_s1_ur_mem : rev68_s1_ur.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane13 rev68_vertex0 rev68_vertex4 rev68_s1_ur
    rev68_vertex0_mem rev68_vertex4_mem (by decide)
theorem rev68_slab1 (p : Point) (hp : p∈IntegerCarrier rev68_planes)
    (hx0 : rev68_s1_ll.real.1≤p.1) (hx1 : p.1≤rev68_s1_lr.real.1) :
    p∈rationalHull (fractionRow68.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev68_plane31 rev68_plane13 rev68_s1_ll rev68_s1_lr rev68_s1_ul rev68_s1_ur
    (by decide) rev68_s1_ll_mem rev68_s1_lr_mem rev68_s1_ul_mem rev68_s1_ur_mem p
    (hp _ rev68_plane31_mem) (hp _ rev68_plane13_mem) hx0 hx1
def rev68_s2_ll : FractionPoint := ⟨43512237817069867,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev68_s2_ll_mem : rev68_s2_ll.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane26 rev68_vertex2 rev68_vertex3 rev68_s2_ll
    rev68_vertex2_mem rev68_vertex3_mem (by decide)
def rev68_s2_lr : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev68_s2_lr_mem : rev68_s2_lr.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane26 rev68_vertex2 rev68_vertex3 rev68_s2_lr
    rev68_vertex2_mem rev68_vertex3_mem (by decide)
def rev68_s2_ul : FractionPoint := ⟨43512237817069867,162301238908000000,2065685038825564714777,4630616647284148000000⟩
theorem rev68_s2_ul_mem : rev68_s2_ul.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane13 rev68_vertex0 rev68_vertex4 rev68_s2_ul
    rev68_vertex0_mem rev68_vertex4_mem (by decide)
def rev68_s2_ur : FractionPoint := ⟨50875247919,183754000000,2339812373536801,5242685374000000⟩
theorem rev68_s2_ur_mem : rev68_s2_ur.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane13 rev68_vertex0 rev68_vertex4 rev68_s2_ur
    rev68_vertex0_mem rev68_vertex4_mem (by decide)
theorem rev68_slab2 (p : Point) (hp : p∈IntegerCarrier rev68_planes)
    (hx0 : rev68_s2_ll.real.1≤p.1) (hx1 : p.1≤rev68_s2_lr.real.1) :
    p∈rationalHull (fractionRow68.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev68_plane26 rev68_plane13 rev68_s2_ll rev68_s2_lr rev68_s2_ul rev68_s2_ur
    (by decide) rev68_s2_ll_mem rev68_s2_lr_mem rev68_s2_ul_mem rev68_s2_ur_mem p
    (hp _ rev68_plane26_mem) (hp _ rev68_plane13_mem) hx0 hx1
def rev68_s3_ll : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev68_s3_ll_mem : rev68_s3_ll.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane50 rev68_vertex3 rev68_vertex4 rev68_s3_ll
    rev68_vertex3_mem rev68_vertex4_mem (by decide)
def rev68_s3_lr : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev68_s3_lr_mem : rev68_s3_lr.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane50 rev68_vertex3 rev68_vertex4 rev68_s3_lr
    rev68_vertex3_mem rev68_vertex4_mem (by decide)
def rev68_s3_ul : FractionPoint := ⟨50875247919,183754000000,2339812373536801,5242685374000000⟩
theorem rev68_s3_ul_mem : rev68_s3_ul.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane13 rev68_vertex0 rev68_vertex4 rev68_s3_ul
    rev68_vertex0_mem rev68_vertex4_mem (by decide)
def rev68_s3_ur : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev68_s3_ur_mem : rev68_s3_ur.real ∈ rationalHull (fractionRow68.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow68 rev68_plane13 rev68_vertex0 rev68_vertex4 rev68_s3_ur
    rev68_vertex0_mem rev68_vertex4_mem (by decide)
theorem rev68_slab3 (p : Point) (hp : p∈IntegerCarrier rev68_planes)
    (hx0 : rev68_s3_ll.real.1≤p.1) (hx1 : p.1≤rev68_s3_lr.real.1) :
    p∈rationalHull (fractionRow68.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev68_plane50 rev68_plane13 rev68_s3_ll rev68_s3_lr rev68_s3_ul rev68_s3_ur
    (by decide) rev68_s3_ll_mem rev68_s3_lr_mem rev68_s3_ul_mem rev68_s3_ur_mem p
    (hp _ rev68_plane50_mem) (hp _ rev68_plane13_mem) hx0 hx1
theorem rev68_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev68_planes) : rev68_s0_ll.real.1≤p.1 := by
  have hc := rev68_plane8.combine_sound rev68_plane31 643972000000 699568000000 (by decide) (by decide) p
    (hp _ rev68_plane8_mem) (hp _ rev68_plane31_mem)
  exact (rev68_plane8.combine rev68_plane31 643972000000 699568000000).xBoundCheck_sound rev68_s0_ll.nx rev68_s0_ll.dx true (by decide) p hc
theorem rev68_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev68_planes) : p.1≤rev68_s3_lr.real.1 := by
  have hc := rev68_plane13.combine_sound rev68_plane50 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev68_plane13_mem) (hp _ rev68_plane50_mem)
  exact (rev68_plane13.combine rev68_plane50 13084000000 2168356000000).xBoundCheck_sound rev68_s3_lr.nx rev68_s3_lr.dx false (by decide) p hc
theorem rev68_hull (p : Point) (hp : p∈IntegerCarrier rev68_planes) :
    p∈rationalHull (fractionRow68.map FractionPoint.rational) := by
  have hxlo := rev68_bound0_lo p hp
  have hxhi := rev68_bound0_hi p hp
  by_cases h0 : p.1≤rev68_s0_lr.real.1
  · exact rev68_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev68_s1_lr.real.1
  · exact rev68_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev68_s2_lr.real.1
  · exact rev68_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev68_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull68 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,6,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow68 := by
  rw [← fractionRow68_correct]
  exact rev68_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull68
