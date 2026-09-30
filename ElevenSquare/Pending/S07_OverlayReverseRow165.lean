import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev165_planes : List IntegerPlane := integerOverlayPlanes ![10,13,13,10]
def rev165_plane32 : IntegerPlane := ⟨2058052000000,(-1574160000000),367887499047⟩
theorem rev165_plane32_mem : rev165_plane32 ∈ rev165_planes := by decide
def rev165_plane33 : IntegerPlane := ⟨13084000000,(-2218132000000),(-1594545024972)⟩
theorem rev165_plane33_mem : rev165_plane33 ∈ rev165_planes := by decide
def rev165_plane52 : IntegerPlane := ⟨(-1574160000000),2058052000000,367887499047⟩
theorem rev165_plane52_mem : rev165_plane52 ∈ rev165_planes := by decide
def rev165_plane53 : IntegerPlane := ⟨(-2218132000000),13084000000,(-1594545024972)⟩
theorem rev165_plane53_mem : rev165_plane53 ∈ rev165_planes := by decide
def rev165_vertex0 : FractionPoint := fractionRow165[0]!
theorem rev165_vertex0_mem : rev165_vertex0∈fractionRow165 := by decide
def rev165_vertex1 : FractionPoint := fractionRow165[1]!
theorem rev165_vertex1_mem : rev165_vertex1∈fractionRow165 := by decide
def rev165_vertex2 : FractionPoint := fractionRow165[2]!
theorem rev165_vertex2_mem : rev165_vertex2∈fractionRow165 := by decide
def rev165_vertex3 : FractionPoint := fractionRow165[3]!
theorem rev165_vertex3_mem : rev165_vertex3∈fractionRow165 := by decide
def rev165_s0_ll : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev165_s0_ll_mem : rev165_s0_ll.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane33 rev165_vertex0 rev165_vertex1 rev165_s0_ll
    rev165_vertex0_mem rev165_vertex1_mem (by decide)
def rev165_s0_lr : FractionPoint := ⟨821617504442801373,1136108672356000000,455581618690233349809591,630009750407589748000000⟩
theorem rev165_s0_lr_mem : rev165_s0_lr.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane33 rev165_vertex0 rev165_vertex1 rev165_s0_lr
    rev165_vertex0_mem rev165_vertex1_mem (by decide)
def rev165_s0_ul : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev165_s0_ul_mem : rev165_s0_ul.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane53 rev165_vertex0 rev165_vertex3 rev165_s0_ul
    rev165_vertex0_mem rev165_vertex3_mem (by decide)
def rev165_s0_ur : FractionPoint := ⟨821617504442801373,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev165_s0_ur_mem : rev165_s0_ur.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane53 rev165_vertex0 rev165_vertex3 rev165_s0_ur
    rev165_vertex0_mem rev165_vertex3_mem (by decide)
theorem rev165_slab0 (p : Point) (hp : p∈IntegerCarrier rev165_planes)
    (hx0 : rev165_s0_ll.real.1≤p.1) (hx1 : p.1≤rev165_s0_lr.real.1) :
    p∈rationalHull (fractionRow165.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev165_plane33 rev165_plane53 rev165_s0_ll rev165_s0_lr rev165_s0_ul rev165_s0_ur
    (by decide) rev165_s0_ll_mem rev165_s0_lr_mem rev165_s0_ul_mem rev165_s0_ur_mem p
    (hp _ rev165_plane33_mem) (hp _ rev165_plane53_mem) hx0 hx1
def rev165_s1_ll : FractionPoint := ⟨821617504442801373,1136108672356000000,455581618690233349809591,630009750407589748000000⟩
theorem rev165_s1_ll_mem : rev165_s1_ll.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane33 rev165_vertex0 rev165_vertex1 rev165_s1_ll
    rev165_vertex0_mem rev165_vertex1_mem (by decide)
def rev165_s1_lr : FractionPoint := ⟨118789001090930133,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev165_s1_lr_mem : rev165_s1_lr.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane33 rev165_vertex0 rev165_vertex1 rev165_s1_lr
    rev165_vertex0_mem rev165_vertex1_mem (by decide)
def rev165_s1_ul : FractionPoint := ⟨821617504442801373,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev165_s1_ul_mem : rev165_s1_ul.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane52 rev165_vertex3 rev165_vertex2 rev165_s1_ul
    rev165_vertex3_mem rev165_vertex2_mem (by decide)
def rev165_s1_ur : FractionPoint := ⟨118789001090930133,162301238908000000,61675372707848086870989,83506097334271804000000⟩
theorem rev165_s1_ur_mem : rev165_s1_ur.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane52 rev165_vertex3 rev165_vertex2 rev165_s1_ur
    rev165_vertex3_mem rev165_vertex2_mem (by decide)
theorem rev165_slab1 (p : Point) (hp : p∈IntegerCarrier rev165_planes)
    (hx0 : rev165_s1_ll.real.1≤p.1) (hx1 : p.1≤rev165_s1_lr.real.1) :
    p∈rationalHull (fractionRow165.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev165_plane33 rev165_plane52 rev165_s1_ll rev165_s1_lr rev165_s1_ul rev165_s1_ur
    (by decide) rev165_s1_ll_mem rev165_s1_lr_mem rev165_s1_ul_mem rev165_s1_ur_mem p
    (hp _ rev165_plane33_mem) (hp _ rev165_plane52_mem) hx0 hx1
def rev165_s2_ll : FractionPoint := ⟨118789001090930133,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev165_s2_ll_mem : rev165_s2_ll.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane32 rev165_vertex1 rev165_vertex2 rev165_s2_ll
    rev165_vertex1_mem rev165_vertex2_mem (by decide)
def rev165_s2_lr : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev165_s2_lr_mem : rev165_s2_lr.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane32 rev165_vertex1 rev165_vertex2 rev165_s2_lr
    rev165_vertex1_mem rev165_vertex2_mem (by decide)
def rev165_s2_ul : FractionPoint := ⟨118789001090930133,162301238908000000,61675372707848086870989,83506097334271804000000⟩
theorem rev165_s2_ul_mem : rev165_s2_ul.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane52 rev165_vertex3 rev165_vertex2 rev165_s2_ul
    rev165_vertex3_mem rev165_vertex2_mem (by decide)
def rev165_s2_ur : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev165_s2_ur_mem : rev165_s2_ur.real ∈ rationalHull (fractionRow165.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow165 rev165_plane52 rev165_vertex3 rev165_vertex2 rev165_s2_ur
    rev165_vertex3_mem rev165_vertex2_mem (by decide)
theorem rev165_slab2 (p : Point) (hp : p∈IntegerCarrier rev165_planes)
    (hx0 : rev165_s2_ll.real.1≤p.1) (hx1 : p.1≤rev165_s2_lr.real.1) :
    p∈rationalHull (fractionRow165.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev165_plane32 rev165_plane52 rev165_s2_ll rev165_s2_lr rev165_s2_ul rev165_s2_ur
    (by decide) rev165_s2_ll_mem rev165_s2_lr_mem rev165_s2_ul_mem rev165_s2_ur_mem p
    (hp _ rev165_plane32_mem) (hp _ rev165_plane52_mem) hx0 hx1
theorem rev165_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev165_planes) : rev165_s0_ll.real.1≤p.1 := by
  have hc := rev165_plane33.combine_sound rev165_plane53 13084000000 2218132000000 (by decide) (by decide) p
    (hp _ rev165_plane33_mem) (hp _ rev165_plane53_mem)
  exact (rev165_plane33.combine rev165_plane53 13084000000 2218132000000).xBoundCheck_sound rev165_s0_ll.nx rev165_s0_ll.dx true (by decide) p hc
theorem rev165_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev165_planes) : p.1≤rev165_s2_lr.real.1 := by
  have hc := rev165_plane32.combine_sound rev165_plane52 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev165_plane32_mem) (hp _ rev165_plane52_mem)
  exact (rev165_plane32.combine rev165_plane52 2058052000000 1574160000000).xBoundCheck_sound rev165_s2_lr.nx rev165_s2_lr.dx false (by decide) p hc
theorem rev165_hull (p : Point) (hp : p∈IntegerCarrier rev165_planes) :
    p∈rationalHull (fractionRow165.map FractionPoint.rational) := by
  have hxlo := rev165_bound0_lo p hp
  have hxhi := rev165_bound0_hi p hp
  by_cases h0 : p.1≤rev165_s0_lr.real.1
  · exact rev165_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev165_s1_lr.real.1
  · exact rev165_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev165_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull165 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow165 := by
  rw [← fractionRow165_correct]
  exact rev165_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull165
