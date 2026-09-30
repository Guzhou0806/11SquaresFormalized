import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev29_planes : List IntegerPlane := integerOverlayPlanes ![2,5,10,13]
def rev29_plane10 : IntegerPlane := ⟨13084000000,2218132000000,623586975028⟩
theorem rev29_plane10_mem : rev29_plane10 ∈ rev29_planes := by decide
def rev29_plane11 : IntegerPlane := ⟨2058052000000,1574160000000,1942047499047⟩
theorem rev29_plane11_mem : rev29_plane11 ∈ rev29_planes := by decide
def rev29_plane72 : IntegerPlane := ⟨(-1574160000000),(-2058052000000),(-1690164500953)⟩
theorem rev29_plane72_mem : rev29_plane72 ∈ rev29_planes := by decide
def rev29_plane73 : IntegerPlane := ⟨(-2218132000000),(-13084000000),(-1607629024972)⟩
theorem rev29_plane73_mem : rev29_plane73 ∈ rev29_planes := by decide
def rev29_vertex0 : FractionPoint := fractionRow29[0]!
theorem rev29_vertex0_mem : rev29_vertex0∈fractionRow29 := by decide
def rev29_vertex1 : FractionPoint := fractionRow29[1]!
theorem rev29_vertex1_mem : rev29_vertex1∈fractionRow29 := by decide
def rev29_vertex2 : FractionPoint := fractionRow29[2]!
theorem rev29_vertex2_mem : rev29_vertex2∈fractionRow29 := by decide
def rev29_vertex3 : FractionPoint := fractionRow29[3]!
theorem rev29_vertex3_mem : rev29_vertex3∈fractionRow29 := by decide
def rev29_s0_ll : FractionPoint := ⟨132878752081,183754000000,50875247919,183754000000⟩
theorem rev29_s0_ll_mem : rev29_s0_ll.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane73 rev29_vertex2 rev29_vertex3 rev29_s0_ll
    rev29_vertex2_mem rev29_vertex3_mem (by decide)
def rev29_s0_lr : FractionPoint := ⟨821617504442801373,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev29_s0_lr_mem : rev29_s0_lr.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane73 rev29_vertex2 rev29_vertex3 rev29_s0_lr
    rev29_vertex2_mem rev29_vertex3_mem (by decide)
def rev29_s0_ul : FractionPoint := ⟨132878752081,183754000000,50875247919,183754000000⟩
theorem rev29_s0_ul_mem : rev29_s0_ul.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane10 rev29_vertex2 rev29_vertex1 rev29_s0_ul
    rev29_vertex2_mem rev29_vertex1_mem (by decide)
def rev29_s0_ur : FractionPoint := ⟨821617504442801373,1136108672356000000,174428131717356398190409,630009750407589748000000⟩
theorem rev29_s0_ur_mem : rev29_s0_ur.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane10 rev29_vertex2 rev29_vertex1 rev29_s0_ur
    rev29_vertex2_mem rev29_vertex1_mem (by decide)
theorem rev29_slab0 (p : Point) (hp : p∈IntegerCarrier rev29_planes)
    (hx0 : rev29_s0_ll.real.1≤p.1) (hx1 : p.1≤rev29_s0_lr.real.1) :
    p∈rationalHull (fractionRow29.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev29_plane73 rev29_plane10 rev29_s0_ll rev29_s0_lr rev29_s0_ul rev29_s0_ur
    (by decide) rev29_s0_ll_mem rev29_s0_lr_mem rev29_s0_ul_mem rev29_s0_ur_mem p
    (hp _ rev29_plane73_mem) (hp _ rev29_plane10_mem) hx0 hx1
def rev29_s1_ll : FractionPoint := ⟨821617504442801373,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev29_s1_ll_mem : rev29_s1_ll.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane72 rev29_vertex3 rev29_vertex0 rev29_s1_ll
    rev29_vertex3_mem rev29_vertex0_mem (by decide)
def rev29_s1_lr : FractionPoint := ⟨118789001090930133,162301238908000000,21830724626423717129011,83506097334271804000000⟩
theorem rev29_s1_lr_mem : rev29_s1_lr.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane72 rev29_vertex3 rev29_vertex0 rev29_s1_lr
    rev29_vertex3_mem rev29_vertex0_mem (by decide)
def rev29_s1_ul : FractionPoint := ⟨821617504442801373,1136108672356000000,174428131717356398190409,630009750407589748000000⟩
theorem rev29_s1_ul_mem : rev29_s1_ul.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane10 rev29_vertex2 rev29_vertex1 rev29_s1_ul
    rev29_vertex2_mem rev29_vertex1_mem (by decide)
def rev29_s1_ur : FractionPoint := ⟨118789001090930133,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev29_s1_ur_mem : rev29_s1_ur.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane10 rev29_vertex2 rev29_vertex1 rev29_s1_ur
    rev29_vertex2_mem rev29_vertex1_mem (by decide)
theorem rev29_slab1 (p : Point) (hp : p∈IntegerCarrier rev29_planes)
    (hx0 : rev29_s1_ll.real.1≤p.1) (hx1 : p.1≤rev29_s1_lr.real.1) :
    p∈rationalHull (fractionRow29.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev29_plane72 rev29_plane10 rev29_s1_ll rev29_s1_lr rev29_s1_ul rev29_s1_ur
    (by decide) rev29_s1_ll_mem rev29_s1_lr_mem rev29_s1_ul_mem rev29_s1_ur_mem p
    (hp _ rev29_plane72_mem) (hp _ rev29_plane10_mem) hx0 hx1
def rev29_s2_ll : FractionPoint := ⟨118789001090930133,162301238908000000,21830724626423717129011,83506097334271804000000⟩
theorem rev29_s2_ll_mem : rev29_s2_ll.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane72 rev29_vertex3 rev29_vertex0 rev29_s2_ll
    rev29_vertex3_mem rev29_vertex0_mem (by decide)
def rev29_s2_lr : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev29_s2_lr_mem : rev29_s2_lr.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane72 rev29_vertex3 rev29_vertex0 rev29_s2_lr
    rev29_vertex3_mem rev29_vertex0_mem (by decide)
def rev29_s2_ul : FractionPoint := ⟨118789001090930133,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev29_s2_ul_mem : rev29_s2_ul.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane11 rev29_vertex1 rev29_vertex0 rev29_s2_ul
    rev29_vertex1_mem rev29_vertex0_mem (by decide)
def rev29_s2_ur : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev29_s2_ur_mem : rev29_s2_ur.real ∈ rationalHull (fractionRow29.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow29 rev29_plane11 rev29_vertex1 rev29_vertex0 rev29_s2_ur
    rev29_vertex1_mem rev29_vertex0_mem (by decide)
theorem rev29_slab2 (p : Point) (hp : p∈IntegerCarrier rev29_planes)
    (hx0 : rev29_s2_ll.real.1≤p.1) (hx1 : p.1≤rev29_s2_lr.real.1) :
    p∈rationalHull (fractionRow29.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev29_plane72 rev29_plane11 rev29_s2_ll rev29_s2_lr rev29_s2_ul rev29_s2_ur
    (by decide) rev29_s2_ll_mem rev29_s2_lr_mem rev29_s2_ul_mem rev29_s2_ur_mem p
    (hp _ rev29_plane72_mem) (hp _ rev29_plane11_mem) hx0 hx1
theorem rev29_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev29_planes) : rev29_s0_ll.real.1≤p.1 := by
  have hc := rev29_plane10.combine_sound rev29_plane73 13084000000 2218132000000 (by decide) (by decide) p
    (hp _ rev29_plane10_mem) (hp _ rev29_plane73_mem)
  exact (rev29_plane10.combine rev29_plane73 13084000000 2218132000000).xBoundCheck_sound rev29_s0_ll.nx rev29_s0_ll.dx true (by decide) p hc
theorem rev29_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev29_planes) : p.1≤rev29_s2_lr.real.1 := by
  have hc := rev29_plane11.combine_sound rev29_plane72 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev29_plane11_mem) (hp _ rev29_plane72_mem)
  exact (rev29_plane11.combine rev29_plane72 2058052000000 1574160000000).xBoundCheck_sound rev29_s2_lr.nx rev29_s2_lr.dx false (by decide) p hc
theorem rev29_hull (p : Point) (hp : p∈IntegerCarrier rev29_planes) :
    p∈rationalHull (fractionRow29.map FractionPoint.rational) := by
  have hxlo := rev29_bound0_lo p hp
  have hxhi := rev29_bound0_hi p hp
  by_cases h0 : p.1≤rev29_s0_lr.real.1
  · exact rev29_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev29_s1_lr.real.1
  · exact rev29_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev29_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull29 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow29 := by
  rw [← fractionRow29_correct]
  exact rev29_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull29
