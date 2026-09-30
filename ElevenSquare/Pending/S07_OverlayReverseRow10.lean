import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev10_planes : List IntegerPlane := integerOverlayPlanes ![0,7,7,0]
def rev10_plane9 : IntegerPlane := ⟨2129316000000,1440116000000,827972119784⟩
theorem rev10_plane9_mem : rev10_plane9 ∈ rev10_planes := by decide
def rev10_plane27 : IntegerPlane := ⟨202532000000,(-1861776000000),(-383371739447)⟩
theorem rev10_plane27_mem : rev10_plane27 ∈ rev10_planes := by decide
def rev10_plane47 : IntegerPlane := ⟨(-1861776000000),202532000000,(-383371739447)⟩
theorem rev10_plane47_mem : rev10_plane47 ∈ rev10_planes := by decide
def rev10_plane69 : IntegerPlane := ⟨1440116000000,2129316000000,827972119784⟩
theorem rev10_plane69_mem : rev10_plane69 ∈ rev10_planes := by decide
def rev10_vertex0 : FractionPoint := fractionRow10[0]!
theorem rev10_vertex0_mem : rev10_vertex0∈fractionRow10 := by decide
def rev10_vertex1 : FractionPoint := fractionRow10[1]!
theorem rev10_vertex1_mem : rev10_vertex1∈fractionRow10 := by decide
def rev10_vertex2 : FractionPoint := fractionRow10[2]!
theorem rev10_vertex2_mem : rev10_vertex2∈fractionRow10 := by decide
def rev10_vertex3 : FractionPoint := fractionRow10[3]!
theorem rev10_vertex3_mem : rev10_vertex3∈fractionRow10 := by decide
def rev10_s0_ll : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev10_s0_ll_mem : rev10_s0_ll.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane27 rev10_vertex3 rev10_vertex0 rev10_s0_ll
    rev10_vertex3_mem rev10_vertex0_mem (by decide)
def rev10_s0_lr : FractionPoint := ⟨49200521405821067,212798949946400000,57216114746756379848303,247614986147130504000000⟩
theorem rev10_s0_lr_mem : rev10_s0_lr.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane27 rev10_vertex3 rev10_vertex0 rev10_s0_lr
    rev10_vertex3_mem rev10_vertex0_mem (by decide)
def rev10_s0_ul : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev10_s0_ul_mem : rev10_s0_ul.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane47 rev10_vertex3 rev10_vertex2 rev10_s0_ul
    rev10_vertex3_mem rev10_vertex2_mem (by decide)
def rev10_s0_ur : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev10_s0_ur_mem : rev10_s0_ur.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane47 rev10_vertex3 rev10_vertex2 rev10_s0_ur
    rev10_vertex3_mem rev10_vertex2_mem (by decide)
theorem rev10_slab0 (p : Point) (hp : p∈IntegerCarrier rev10_planes)
    (hx0 : rev10_s0_ll.real.1≤p.1) (hx1 : p.1≤rev10_s0_lr.real.1) :
    p∈rationalHull (fractionRow10.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev10_plane27 rev10_plane47 rev10_s0_ll rev10_s0_lr rev10_s0_ul rev10_s0_ur
    (by decide) rev10_s0_ll_mem rev10_s0_lr_mem rev10_s0_ul_mem rev10_s0_ur_mem p
    (hp _ rev10_plane27_mem) (hp _ rev10_plane47_mem) hx0 hx1
def rev10_s1_ll : FractionPoint := ⟨49200521405821067,212798949946400000,57216114746756379848303,247614986147130504000000⟩
theorem rev10_s1_ll_mem : rev10_s1_ll.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane27 rev10_vertex3 rev10_vertex0 rev10_s1_ll
    rev10_vertex3_mem rev10_vertex0_mem (by decide)
def rev10_s1_lr : FractionPoint := ⟨103496514973,446179000000,192013775505234649,830685353904000000⟩
theorem rev10_s1_lr_mem : rev10_s1_lr.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane27 rev10_vertex3 rev10_vertex0 rev10_s1_lr
    rev10_vertex3_mem rev10_vertex0_mem (by decide)
def rev10_s1_ul : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev10_s1_ul_mem : rev10_s1_ul.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane69 rev10_vertex2 rev10_vertex1 rev10_s1_ul
    rev10_vertex2_mem rev10_vertex1_mem (by decide)
def rev10_s1_ur : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev10_s1_ur_mem : rev10_s1_ur.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane69 rev10_vertex2 rev10_vertex1 rev10_s1_ur
    rev10_vertex2_mem rev10_vertex1_mem (by decide)
theorem rev10_slab1 (p : Point) (hp : p∈IntegerCarrier rev10_planes)
    (hx0 : rev10_s1_ll.real.1≤p.1) (hx1 : p.1≤rev10_s1_lr.real.1) :
    p∈rationalHull (fractionRow10.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev10_plane27 rev10_plane69 rev10_s1_ll rev10_s1_lr rev10_s1_ul rev10_s1_ur
    (by decide) rev10_s1_ll_mem rev10_s1_lr_mem rev10_s1_ul_mem rev10_s1_ur_mem p
    (hp _ rev10_plane27_mem) (hp _ rev10_plane69_mem) hx0 hx1
def rev10_s2_ll : FractionPoint := ⟨103496514973,446179000000,192013775505234649,830685353904000000⟩
theorem rev10_s2_ll_mem : rev10_s2_ll.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane27 rev10_vertex3 rev10_vertex0 rev10_s2_ll
    rev10_vertex3_mem rev10_vertex0_mem (by decide)
def rev10_s2_lr : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev10_s2_lr_mem : rev10_s2_lr.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane27 rev10_vertex3 rev10_vertex0 rev10_s2_lr
    rev10_vertex3_mem rev10_vertex0_mem (by decide)
def rev10_s2_ul : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev10_s2_ul_mem : rev10_s2_ul.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane9 rev10_vertex1 rev10_vertex0 rev10_s2_ul
    rev10_vertex1_mem rev10_vertex0_mem (by decide)
def rev10_s2_ur : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev10_s2_ur_mem : rev10_s2_ur.real ∈ rationalHull (fractionRow10.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow10 rev10_plane9 rev10_vertex1 rev10_vertex0 rev10_s2_ur
    rev10_vertex1_mem rev10_vertex0_mem (by decide)
theorem rev10_slab2 (p : Point) (hp : p∈IntegerCarrier rev10_planes)
    (hx0 : rev10_s2_ll.real.1≤p.1) (hx1 : p.1≤rev10_s2_lr.real.1) :
    p∈rationalHull (fractionRow10.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev10_plane27 rev10_plane9 rev10_s2_ll rev10_s2_lr rev10_s2_ul rev10_s2_ur
    (by decide) rev10_s2_ll_mem rev10_s2_lr_mem rev10_s2_ul_mem rev10_s2_ur_mem p
    (hp _ rev10_plane27_mem) (hp _ rev10_plane9_mem) hx0 hx1
theorem rev10_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev10_planes) : rev10_s0_ll.real.1≤p.1 := by
  have hc := rev10_plane27.combine_sound rev10_plane47 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev10_plane27_mem) (hp _ rev10_plane47_mem)
  exact (rev10_plane27.combine rev10_plane47 202532000000 1861776000000).xBoundCheck_sound rev10_s0_ll.nx rev10_s0_ll.dx true (by decide) p hc
theorem rev10_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev10_planes) : p.1≤rev10_s2_lr.real.1 := by
  have hc := rev10_plane9.combine_sound rev10_plane27 1861776000000 1440116000000 (by decide) (by decide) p
    (hp _ rev10_plane9_mem) (hp _ rev10_plane27_mem)
  exact (rev10_plane9.combine rev10_plane27 1861776000000 1440116000000).xBoundCheck_sound rev10_s2_lr.nx rev10_s2_lr.dx false (by decide) p hc
theorem rev10_hull (p : Point) (hp : p∈IntegerCarrier rev10_planes) :
    p∈rationalHull (fractionRow10.map FractionPoint.rational) := by
  have hxlo := rev10_bound0_lo p hp
  have hxhi := rev10_bound0_hi p hp
  by_cases h0 : p.1≤rev10_s0_lr.real.1
  · exact rev10_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev10_s1_lr.real.1
  · exact rev10_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev10_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull10 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow10 := by
  rw [← fractionRow10_correct]
  exact rev10_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull10
