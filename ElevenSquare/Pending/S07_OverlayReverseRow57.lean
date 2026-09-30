import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev57_planes : List IntegerPlane := integerOverlayPlanes ![5,2,6,9]
def rev57_plane29 : IntegerPlane := ⟨2099728000000,1393416000000,1359544139484⟩
theorem rev57_plane29_mem : rev57_plane29 ∈ rev57_planes := by decide
def rev57_plane30 : IntegerPlane := ⟨(-13084000000),2218132000000,610502975028⟩
theorem rev57_plane30_mem : rev57_plane30 ∈ rev57_planes := by decide
def rev57_plane68 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-1212544726896)⟩
theorem rev57_plane68_mem : rev57_plane68 ∈ rev57_planes := by decide
def rev57_plane69 : IntegerPlane := ⟨(-2168356000000),51300000000,(-953534835544)⟩
theorem rev57_plane69_mem : rev57_plane69 ∈ rev57_planes := by decide
def rev57_vertex0 : FractionPoint := fractionRow57[0]!
theorem rev57_vertex0_mem : rev57_vertex0∈fractionRow57 := by decide
def rev57_vertex1 : FractionPoint := fractionRow57[1]!
theorem rev57_vertex1_mem : rev57_vertex1∈fractionRow57 := by decide
def rev57_vertex2 : FractionPoint := fractionRow57[2]!
theorem rev57_vertex2_mem : rev57_vertex2∈fractionRow57 := by decide
def rev57_vertex3 : FractionPoint := fractionRow57[3]!
theorem rev57_vertex3_mem : rev57_vertex3∈fractionRow57 := by decide
def rev57_s0_ll : FractionPoint := ⟨3270661284241,7332499000000,29287950748577,109987485000000⟩
theorem rev57_s0_ll_mem : rev57_s0_ll.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane68 rev57_vertex3 rev57_vertex0 rev57_s0_ll
    rev57_vertex3_mem rev57_vertex0_mem (by decide)
def rev57_s0_lr : FractionPoint := ⟨7060476758071777,15819173098000000,734259282275019253961,2759417459349630000000⟩
theorem rev57_s0_lr_mem : rev57_s0_lr.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane68 rev57_vertex3 rev57_vertex0 rev57_s0_lr
    rev57_vertex3_mem rev57_vertex0_mem (by decide)
def rev57_s0_ul : FractionPoint := ⟨3270661284241,7332499000000,29287950748577,109987485000000⟩
theorem rev57_s0_ul_mem : rev57_s0_ul.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane69 rev57_vertex3 rev57_vertex2 rev57_s0_ul
    rev57_vertex3_mem rev57_vertex2_mem (by decide)
def rev57_s0_ur : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev57_s0_ur_mem : rev57_s0_ur.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane69 rev57_vertex3 rev57_vertex2 rev57_s0_ur
    rev57_vertex3_mem rev57_vertex2_mem (by decide)
theorem rev57_slab0 (p : Point) (hp : p∈IntegerCarrier rev57_planes)
    (hx0 : rev57_s0_ll.real.1≤p.1) (hx1 : p.1≤rev57_s0_lr.real.1) :
    p∈rationalHull (fractionRow57.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev57_plane68 rev57_plane69 rev57_s0_ll rev57_s0_lr rev57_s0_ul rev57_s0_ur
    (by decide) rev57_s0_ll_mem rev57_s0_lr_mem rev57_s0_ul_mem rev57_s0_ur_mem p
    (hp _ rev57_plane68_mem) (hp _ rev57_plane69_mem) hx0 hx1
def rev57_s1_ll : FractionPoint := ⟨7060476758071777,15819173098000000,734259282275019253961,2759417459349630000000⟩
theorem rev57_s1_ll_mem : rev57_s1_ll.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane68 rev57_vertex3 rev57_vertex0 rev57_s1_ll
    rev57_vertex3_mem rev57_vertex0_mem (by decide)
def rev57_s1_lr : FractionPoint := ⟨27062046846878853,58446316538000000,2593363605042740122157,10195083225306030000000⟩
theorem rev57_s1_lr_mem : rev57_s1_lr.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane68 rev57_vertex3 rev57_vertex0 rev57_s1_lr
    rev57_vertex3_mem rev57_vertex0_mem (by decide)
def rev57_s1_ul : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev57_s1_ul_mem : rev57_s1_ul.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane30 rev57_vertex2 rev57_vertex1 rev57_s1_ul
    rev57_vertex2_mem rev57_vertex1_mem (by decide)
def rev57_s1_ur : FractionPoint := ⟨27062046846878853,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev57_s1_ur_mem : rev57_s1_ur.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane30 rev57_vertex2 rev57_vertex1 rev57_s1_ur
    rev57_vertex2_mem rev57_vertex1_mem (by decide)
theorem rev57_slab1 (p : Point) (hp : p∈IntegerCarrier rev57_planes)
    (hx0 : rev57_s1_ll.real.1≤p.1) (hx1 : p.1≤rev57_s1_lr.real.1) :
    p∈rationalHull (fractionRow57.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev57_plane68 rev57_plane30 rev57_s1_ll rev57_s1_lr rev57_s1_ul rev57_s1_ur
    (by decide) rev57_s1_ll_mem rev57_s1_lr_mem rev57_s1_ul_mem rev57_s1_ur_mem p
    (hp _ rev57_plane68_mem) (hp _ rev57_plane30_mem) hx0 hx1
def rev57_s2_ll : FractionPoint := ⟨27062046846878853,58446316538000000,2593363605042740122157,10195083225306030000000⟩
theorem rev57_s2_ll_mem : rev57_s2_ll.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane68 rev57_vertex3 rev57_vertex0 rev57_s2_ll
    rev57_vertex3_mem rev57_vertex0_mem (by decide)
def rev57_s2_lr : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev57_s2_lr_mem : rev57_s2_lr.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane68 rev57_vertex3 rev57_vertex0 rev57_s2_lr
    rev57_vertex3_mem rev57_vertex0_mem (by decide)
def rev57_s2_ul : FractionPoint := ⟨27062046846878853,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev57_s2_ul_mem : rev57_s2_ul.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane29 rev57_vertex1 rev57_vertex0 rev57_s2_ul
    rev57_vertex1_mem rev57_vertex0_mem (by decide)
def rev57_s2_ur : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev57_s2_ur_mem : rev57_s2_ur.real ∈ rationalHull (fractionRow57.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow57 rev57_plane29 rev57_vertex1 rev57_vertex0 rev57_s2_ur
    rev57_vertex1_mem rev57_vertex0_mem (by decide)
theorem rev57_slab2 (p : Point) (hp : p∈IntegerCarrier rev57_planes)
    (hx0 : rev57_s2_ll.real.1≤p.1) (hx1 : p.1≤rev57_s2_lr.real.1) :
    p∈rationalHull (fractionRow57.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev57_plane68 rev57_plane29 rev57_s2_ll rev57_s2_lr rev57_s2_ul rev57_s2_ur
    (by decide) rev57_s2_ll_mem rev57_s2_lr_mem rev57_s2_ul_mem rev57_s2_ur_mem p
    (hp _ rev57_plane68_mem) (hp _ rev57_plane29_mem) hx0 hx1
theorem rev57_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev57_planes) : rev57_s0_ll.real.1≤p.1 := by
  have hc := rev57_plane68.combine_sound rev57_plane69 51300000000 2093220000000 (by decide) (by decide) p
    (hp _ rev57_plane68_mem) (hp _ rev57_plane69_mem)
  exact (rev57_plane68.combine rev57_plane69 51300000000 2093220000000).xBoundCheck_sound rev57_s0_ll.nx rev57_s0_ll.dx true (by decide) p hc
theorem rev57_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev57_planes) : p.1≤rev57_s2_lr.real.1 := by
  have hc := rev57_plane29.combine_sound rev57_plane68 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev57_plane29_mem) (hp _ rev57_plane68_mem)
  exact (rev57_plane29.combine rev57_plane68 2093220000000 1393416000000).xBoundCheck_sound rev57_s2_lr.nx rev57_s2_lr.dx false (by decide) p hc
theorem rev57_hull (p : Point) (hp : p∈IntegerCarrier rev57_planes) :
    p∈rationalHull (fractionRow57.map FractionPoint.rational) := by
  have hxlo := rev57_bound0_lo p hp
  have hxhi := rev57_bound0_hi p hp
  by_cases h0 : p.1≤rev57_s0_lr.real.1
  · exact rev57_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev57_s1_lr.real.1
  · exact rev57_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev57_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull57 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow57 := by
  rw [← fractionRow57_correct]
  exact rev57_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull57
