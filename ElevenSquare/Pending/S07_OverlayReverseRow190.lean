import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev190_planes : List IntegerPlane := integerOverlayPlanes ![13,10,5,2]
def rev190_plane12 : IntegerPlane := ⟨(-2058052000000),(-1574160000000),(-1690164500953)⟩
theorem rev190_plane12_mem : rev190_plane12 ∈ rev190_planes := by decide
def rev190_plane13 : IntegerPlane := ⟨(-13084000000),(-2218132000000),(-1607629024972)⟩
theorem rev190_plane13_mem : rev190_plane13 ∈ rev190_planes := by decide
def rev190_plane70 : IntegerPlane := ⟨2218132000000,13084000000,623586975028⟩
theorem rev190_plane70_mem : rev190_plane70 ∈ rev190_planes := by decide
def rev190_plane71 : IntegerPlane := ⟨1574160000000,2058052000000,1942047499047⟩
theorem rev190_plane71_mem : rev190_plane71 ∈ rev190_planes := by decide
def rev190_vertex0 : FractionPoint := fractionRow190[0]!
theorem rev190_vertex0_mem : rev190_vertex0∈fractionRow190 := by decide
def rev190_vertex1 : FractionPoint := fractionRow190[1]!
theorem rev190_vertex1_mem : rev190_vertex1∈fractionRow190 := by decide
def rev190_vertex2 : FractionPoint := fractionRow190[2]!
theorem rev190_vertex2_mem : rev190_vertex2∈fractionRow190 := by decide
def rev190_vertex3 : FractionPoint := fractionRow190[3]!
theorem rev190_vertex3_mem : rev190_vertex3∈fractionRow190 := by decide
def rev190_s0_ll : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev190_s0_ll_mem : rev190_s0_ll.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane12 rev190_vertex0 rev190_vertex1 rev190_s0_ll
    rev190_vertex0_mem rev190_vertex1_mem (by decide)
def rev190_s0_lr : FractionPoint := ⟨43512237817069867,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev190_s0_lr_mem : rev190_s0_lr.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane12 rev190_vertex0 rev190_vertex1 rev190_s0_lr
    rev190_vertex0_mem rev190_vertex1_mem (by decide)
def rev190_s0_ul : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev190_s0_ul_mem : rev190_s0_ul.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane71 rev190_vertex0 rev190_vertex3 rev190_s0_ul
    rev190_vertex0_mem rev190_vertex3_mem (by decide)
def rev190_s0_ur : FractionPoint := ⟨43512237817069867,162301238908000000,61675372707848086870989,83506097334271804000000⟩
theorem rev190_s0_ur_mem : rev190_s0_ur.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane71 rev190_vertex0 rev190_vertex3 rev190_s0_ur
    rev190_vertex0_mem rev190_vertex3_mem (by decide)
theorem rev190_slab0 (p : Point) (hp : p∈IntegerCarrier rev190_planes)
    (hx0 : rev190_s0_ll.real.1≤p.1) (hx1 : p.1≤rev190_s0_lr.real.1) :
    p∈rationalHull (fractionRow190.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev190_plane12 rev190_plane71 rev190_s0_ll rev190_s0_lr rev190_s0_ul rev190_s0_ur
    (by decide) rev190_s0_ll_mem rev190_s0_lr_mem rev190_s0_ul_mem rev190_s0_ur_mem p
    (hp _ rev190_plane12_mem) (hp _ rev190_plane71_mem) hx0 hx1
def rev190_s1_ll : FractionPoint := ⟨43512237817069867,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev190_s1_ll_mem : rev190_s1_ll.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane13 rev190_vertex1 rev190_vertex2 rev190_s1_ll
    rev190_vertex1_mem rev190_vertex2_mem (by decide)
def rev190_s1_lr : FractionPoint := ⟨314491167913198627,1136108672356000000,455581618690233349809591,630009750407589748000000⟩
theorem rev190_s1_lr_mem : rev190_s1_lr.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane13 rev190_vertex1 rev190_vertex2 rev190_s1_lr
    rev190_vertex1_mem rev190_vertex2_mem (by decide)
def rev190_s1_ul : FractionPoint := ⟨43512237817069867,162301238908000000,61675372707848086870989,83506097334271804000000⟩
theorem rev190_s1_ul_mem : rev190_s1_ul.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane71 rev190_vertex0 rev190_vertex3 rev190_s1_ul
    rev190_vertex0_mem rev190_vertex3_mem (by decide)
def rev190_s1_ur : FractionPoint := ⟨314491167913198627,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev190_s1_ur_mem : rev190_s1_ur.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane71 rev190_vertex0 rev190_vertex3 rev190_s1_ur
    rev190_vertex0_mem rev190_vertex3_mem (by decide)
theorem rev190_slab1 (p : Point) (hp : p∈IntegerCarrier rev190_planes)
    (hx0 : rev190_s1_ll.real.1≤p.1) (hx1 : p.1≤rev190_s1_lr.real.1) :
    p∈rationalHull (fractionRow190.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev190_plane13 rev190_plane71 rev190_s1_ll rev190_s1_lr rev190_s1_ul rev190_s1_ur
    (by decide) rev190_s1_ll_mem rev190_s1_lr_mem rev190_s1_ul_mem rev190_s1_ur_mem p
    (hp _ rev190_plane13_mem) (hp _ rev190_plane71_mem) hx0 hx1
def rev190_s2_ll : FractionPoint := ⟨314491167913198627,1136108672356000000,455581618690233349809591,630009750407589748000000⟩
theorem rev190_s2_ll_mem : rev190_s2_ll.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane13 rev190_vertex1 rev190_vertex2 rev190_s2_ll
    rev190_vertex1_mem rev190_vertex2_mem (by decide)
def rev190_s2_lr : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev190_s2_lr_mem : rev190_s2_lr.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane13 rev190_vertex1 rev190_vertex2 rev190_s2_lr
    rev190_vertex1_mem rev190_vertex2_mem (by decide)
def rev190_s2_ul : FractionPoint := ⟨314491167913198627,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev190_s2_ul_mem : rev190_s2_ul.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane70 rev190_vertex3 rev190_vertex2 rev190_s2_ul
    rev190_vertex3_mem rev190_vertex2_mem (by decide)
def rev190_s2_ur : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev190_s2_ur_mem : rev190_s2_ur.real ∈ rationalHull (fractionRow190.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow190 rev190_plane70 rev190_vertex3 rev190_vertex2 rev190_s2_ur
    rev190_vertex3_mem rev190_vertex2_mem (by decide)
theorem rev190_slab2 (p : Point) (hp : p∈IntegerCarrier rev190_planes)
    (hx0 : rev190_s2_ll.real.1≤p.1) (hx1 : p.1≤rev190_s2_lr.real.1) :
    p∈rationalHull (fractionRow190.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev190_plane13 rev190_plane70 rev190_s2_ll rev190_s2_lr rev190_s2_ul rev190_s2_ur
    (by decide) rev190_s2_ll_mem rev190_s2_lr_mem rev190_s2_ul_mem rev190_s2_ur_mem p
    (hp _ rev190_plane13_mem) (hp _ rev190_plane70_mem) hx0 hx1
theorem rev190_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev190_planes) : rev190_s0_ll.real.1≤p.1 := by
  have hc := rev190_plane12.combine_sound rev190_plane71 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev190_plane12_mem) (hp _ rev190_plane71_mem)
  exact (rev190_plane12.combine rev190_plane71 2058052000000 1574160000000).xBoundCheck_sound rev190_s0_ll.nx rev190_s0_ll.dx true (by decide) p hc
theorem rev190_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev190_planes) : p.1≤rev190_s2_lr.real.1 := by
  have hc := rev190_plane13.combine_sound rev190_plane70 13084000000 2218132000000 (by decide) (by decide) p
    (hp _ rev190_plane13_mem) (hp _ rev190_plane70_mem)
  exact (rev190_plane13.combine rev190_plane70 13084000000 2218132000000).xBoundCheck_sound rev190_s2_lr.nx rev190_s2_lr.dx false (by decide) p hc
theorem rev190_hull (p : Point) (hp : p∈IntegerCarrier rev190_planes) :
    p∈rationalHull (fractionRow190.map FractionPoint.rational) := by
  have hxlo := rev190_bound0_lo p hp
  have hxhi := rev190_bound0_hi p hp
  by_cases h0 : p.1≤rev190_s0_lr.real.1
  · exact rev190_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev190_s1_lr.real.1
  · exact rev190_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev190_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull190 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow190 := by
  rw [← fractionRow190_correct]
  exact rev190_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull190
