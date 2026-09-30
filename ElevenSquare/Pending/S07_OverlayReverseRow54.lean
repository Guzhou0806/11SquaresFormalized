import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev54_planes : List IntegerPlane := integerOverlayPlanes ![5,2,2,5]
def rev54_plane30 : IntegerPlane := ⟨(-13084000000),2218132000000,610502975028⟩
theorem rev54_plane30_mem : rev54_plane30 ∈ rev54_planes := by decide
def rev54_plane31 : IntegerPlane := ⟨(-2058052000000),1574160000000,(-116004500953)⟩
theorem rev54_plane31_mem : rev54_plane31 ∈ rev54_planes := by decide
def rev54_plane50 : IntegerPlane := ⟨2218132000000,(-13084000000),610502975028⟩
theorem rev54_plane50_mem : rev54_plane50 ∈ rev54_planes := by decide
def rev54_plane51 : IntegerPlane := ⟨1574160000000,(-2058052000000),(-116004500953)⟩
theorem rev54_plane51_mem : rev54_plane51 ∈ rev54_planes := by decide
def rev54_vertex0 : FractionPoint := fractionRow54[0]!
theorem rev54_vertex0_mem : rev54_vertex0∈fractionRow54 := by decide
def rev54_vertex1 : FractionPoint := fractionRow54[1]!
theorem rev54_vertex1_mem : rev54_vertex1∈fractionRow54 := by decide
def rev54_vertex2 : FractionPoint := fractionRow54[2]!
theorem rev54_vertex2_mem : rev54_vertex2∈fractionRow54 := by decide
def rev54_vertex3 : FractionPoint := fractionRow54[3]!
theorem rev54_vertex3_mem : rev54_vertex3∈fractionRow54 := by decide
def rev54_s0_ll : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev54_s0_ll_mem : rev54_s0_ll.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane51 rev54_vertex2 rev54_vertex3 rev54_s0_ll
    rev54_vertex2_mem rev54_vertex3_mem (by decide)
def rev54_s0_lr : FractionPoint := ⟨43512237817069867,162301238908000000,21830724626423717129011,83506097334271804000000⟩
theorem rev54_s0_lr_mem : rev54_s0_lr.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane51 rev54_vertex2 rev54_vertex3 rev54_s0_lr
    rev54_vertex2_mem rev54_vertex3_mem (by decide)
def rev54_s0_ul : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev54_s0_ul_mem : rev54_s0_ul.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane31 rev54_vertex2 rev54_vertex1 rev54_s0_ul
    rev54_vertex2_mem rev54_vertex1_mem (by decide)
def rev54_s0_ur : FractionPoint := ⟨43512237817069867,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev54_s0_ur_mem : rev54_s0_ur.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane31 rev54_vertex2 rev54_vertex1 rev54_s0_ur
    rev54_vertex2_mem rev54_vertex1_mem (by decide)
theorem rev54_slab0 (p : Point) (hp : p∈IntegerCarrier rev54_planes)
    (hx0 : rev54_s0_ll.real.1≤p.1) (hx1 : p.1≤rev54_s0_lr.real.1) :
    p∈rationalHull (fractionRow54.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev54_plane51 rev54_plane31 rev54_s0_ll rev54_s0_lr rev54_s0_ul rev54_s0_ur
    (by decide) rev54_s0_ll_mem rev54_s0_lr_mem rev54_s0_ul_mem rev54_s0_ur_mem p
    (hp _ rev54_plane51_mem) (hp _ rev54_plane31_mem) hx0 hx1
def rev54_s1_ll : FractionPoint := ⟨43512237817069867,162301238908000000,21830724626423717129011,83506097334271804000000⟩
theorem rev54_s1_ll_mem : rev54_s1_ll.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane51 rev54_vertex2 rev54_vertex3 rev54_s1_ll
    rev54_vertex2_mem rev54_vertex3_mem (by decide)
def rev54_s1_lr : FractionPoint := ⟨314491167913198627,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev54_s1_lr_mem : rev54_s1_lr.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane51 rev54_vertex2 rev54_vertex3 rev54_s1_lr
    rev54_vertex2_mem rev54_vertex3_mem (by decide)
def rev54_s1_ul : FractionPoint := ⟨43512237817069867,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev54_s1_ul_mem : rev54_s1_ul.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane30 rev54_vertex1 rev54_vertex0 rev54_s1_ul
    rev54_vertex1_mem rev54_vertex0_mem (by decide)
def rev54_s1_ur : FractionPoint := ⟨314491167913198627,1136108672356000000,174428131717356398190409,630009750407589748000000⟩
theorem rev54_s1_ur_mem : rev54_s1_ur.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane30 rev54_vertex1 rev54_vertex0 rev54_s1_ur
    rev54_vertex1_mem rev54_vertex0_mem (by decide)
theorem rev54_slab1 (p : Point) (hp : p∈IntegerCarrier rev54_planes)
    (hx0 : rev54_s1_ll.real.1≤p.1) (hx1 : p.1≤rev54_s1_lr.real.1) :
    p∈rationalHull (fractionRow54.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev54_plane51 rev54_plane30 rev54_s1_ll rev54_s1_lr rev54_s1_ul rev54_s1_ur
    (by decide) rev54_s1_ll_mem rev54_s1_lr_mem rev54_s1_ul_mem rev54_s1_ur_mem p
    (hp _ rev54_plane51_mem) (hp _ rev54_plane30_mem) hx0 hx1
def rev54_s2_ll : FractionPoint := ⟨314491167913198627,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev54_s2_ll_mem : rev54_s2_ll.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane50 rev54_vertex3 rev54_vertex0 rev54_s2_ll
    rev54_vertex3_mem rev54_vertex0_mem (by decide)
def rev54_s2_lr : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev54_s2_lr_mem : rev54_s2_lr.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane50 rev54_vertex3 rev54_vertex0 rev54_s2_lr
    rev54_vertex3_mem rev54_vertex0_mem (by decide)
def rev54_s2_ul : FractionPoint := ⟨314491167913198627,1136108672356000000,174428131717356398190409,630009750407589748000000⟩
theorem rev54_s2_ul_mem : rev54_s2_ul.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane30 rev54_vertex1 rev54_vertex0 rev54_s2_ul
    rev54_vertex1_mem rev54_vertex0_mem (by decide)
def rev54_s2_ur : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev54_s2_ur_mem : rev54_s2_ur.real ∈ rationalHull (fractionRow54.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow54 rev54_plane30 rev54_vertex1 rev54_vertex0 rev54_s2_ur
    rev54_vertex1_mem rev54_vertex0_mem (by decide)
theorem rev54_slab2 (p : Point) (hp : p∈IntegerCarrier rev54_planes)
    (hx0 : rev54_s2_ll.real.1≤p.1) (hx1 : p.1≤rev54_s2_lr.real.1) :
    p∈rationalHull (fractionRow54.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev54_plane50 rev54_plane30 rev54_s2_ll rev54_s2_lr rev54_s2_ul rev54_s2_ur
    (by decide) rev54_s2_ll_mem rev54_s2_lr_mem rev54_s2_ul_mem rev54_s2_ur_mem p
    (hp _ rev54_plane50_mem) (hp _ rev54_plane30_mem) hx0 hx1
theorem rev54_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev54_planes) : rev54_s0_ll.real.1≤p.1 := by
  have hc := rev54_plane31.combine_sound rev54_plane51 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev54_plane31_mem) (hp _ rev54_plane51_mem)
  exact (rev54_plane31.combine rev54_plane51 2058052000000 1574160000000).xBoundCheck_sound rev54_s0_ll.nx rev54_s0_ll.dx true (by decide) p hc
theorem rev54_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev54_planes) : p.1≤rev54_s2_lr.real.1 := by
  have hc := rev54_plane30.combine_sound rev54_plane50 13084000000 2218132000000 (by decide) (by decide) p
    (hp _ rev54_plane30_mem) (hp _ rev54_plane50_mem)
  exact (rev54_plane30.combine rev54_plane50 13084000000 2218132000000).xBoundCheck_sound rev54_s2_lr.nx rev54_s2_lr.dx false (by decide) p hc
theorem rev54_hull (p : Point) (hp : p∈IntegerCarrier rev54_planes) :
    p∈rationalHull (fractionRow54.map FractionPoint.rational) := by
  have hxlo := rev54_bound0_lo p hp
  have hxhi := rev54_bound0_hi p hp
  by_cases h0 : p.1≤rev54_s0_lr.real.1
  · exact rev54_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev54_s1_lr.real.1
  · exact rev54_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev54_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull54 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow54 := by
  rw [← fractionRow54_correct]
  exact rev54_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull54
