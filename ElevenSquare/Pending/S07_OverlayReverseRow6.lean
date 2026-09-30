import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev6_planes : List IntegerPlane := integerOverlayPlanes ![0,7,2,5]
def rev6_plane8 : IntegerPlane := ⟨(-15204000000),2139684000000,568962228432⟩
theorem rev6_plane8_mem : rev6_plane8 ∈ rev6_planes := by decide
def rev6_plane9 : IntegerPlane := ⟨2129316000000,1440116000000,827972119784⟩
theorem rev6_plane9_mem : rev6_plane9 ∈ rev6_planes := by decide
def rev6_plane47 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-499376240400)⟩
theorem rev6_plane47_mem : rev6_plane47 ∈ rev6_planes := by decide
def rev6_plane64 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-827972119784)⟩
theorem rev6_plane64_mem : rev6_plane64 ∈ rev6_planes := by decide
def rev6_vertex0 : FractionPoint := fractionRow6[0]!
theorem rev6_vertex0_mem : rev6_vertex0∈fractionRow6 := by decide
def rev6_vertex1 : FractionPoint := fractionRow6[1]!
theorem rev6_vertex1_mem : rev6_vertex1∈fractionRow6 := by decide
def rev6_vertex2 : FractionPoint := fractionRow6[2]!
theorem rev6_vertex2_mem : rev6_vertex2∈fractionRow6 := by decide
def rev6_vertex3 : FractionPoint := fractionRow6[3]!
theorem rev6_vertex3_mem : rev6_vertex3∈fractionRow6 := by decide
def rev6_s0_ll : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev6_s0_ll_mem : rev6_s0_ll.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane64 rev6_vertex2 rev6_vertex3 rev6_s0_ll
    rev6_vertex2_mem rev6_vertex3_mem (by decide)
def rev6_s0_lr : FractionPoint := ⟨431262268381943,2073350951000000,91300757421876007433,367901612798293000000⟩
theorem rev6_s0_lr_mem : rev6_s0_lr.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane64 rev6_vertex2 rev6_vertex3 rev6_s0_lr
    rev6_vertex2_mem rev6_vertex3_mem (by decide)
def rev6_s0_ul : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev6_s0_ul_mem : rev6_s0_ul.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane8 rev6_vertex2 rev6_vertex1 rev6_s0_ul
    rev6_vertex2_mem rev6_vertex1_mem (by decide)
def rev6_s0_ur : FractionPoint := ⟨431262268381943,2073350951000000,79198296098933,296192993000000⟩
theorem rev6_s0_ur_mem : rev6_s0_ur.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane8 rev6_vertex2 rev6_vertex1 rev6_s0_ur
    rev6_vertex2_mem rev6_vertex1_mem (by decide)
theorem rev6_slab0 (p : Point) (hp : p∈IntegerCarrier rev6_planes)
    (hx0 : rev6_s0_ll.real.1≤p.1) (hx1 : p.1≤rev6_s0_lr.real.1) :
    p∈rationalHull (fractionRow6.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev6_plane64 rev6_plane8 rev6_s0_ll rev6_s0_lr rev6_s0_ul rev6_s0_ur
    (by decide) rev6_s0_ll_mem rev6_s0_lr_mem rev6_s0_ul_mem rev6_s0_ur_mem p
    (hp _ rev6_plane64_mem) (hp _ rev6_plane8_mem) hx0 hx1
def rev6_s1_ll : FractionPoint := ⟨431262268381943,2073350951000000,91300757421876007433,367901612798293000000⟩
theorem rev6_s1_ll_mem : rev6_s1_ll.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane64 rev6_vertex2 rev6_vertex3 rev6_s1_ll
    rev6_vertex2_mem rev6_vertex3_mem (by decide)
def rev6_s1_lr : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev6_s1_lr_mem : rev6_s1_lr.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane64 rev6_vertex2 rev6_vertex3 rev6_s1_lr
    rev6_vertex2_mem rev6_vertex3_mem (by decide)
def rev6_s1_ul : FractionPoint := ⟨431262268381943,2073350951000000,79198296098933,296192993000000⟩
theorem rev6_s1_ul_mem : rev6_s1_ul.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane9 rev6_vertex1 rev6_vertex0 rev6_s1_ul
    rev6_vertex1_mem rev6_vertex0_mem (by decide)
def rev6_s1_ur : FractionPoint := ⟨1478090653118879,6436683405200000,2727590407806825564641,11586963448453754000000⟩
theorem rev6_s1_ur_mem : rev6_s1_ur.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane9 rev6_vertex1 rev6_vertex0 rev6_s1_ur
    rev6_vertex1_mem rev6_vertex0_mem (by decide)
theorem rev6_slab1 (p : Point) (hp : p∈IntegerCarrier rev6_planes)
    (hx0 : rev6_s1_ll.real.1≤p.1) (hx1 : p.1≤rev6_s1_lr.real.1) :
    p∈rationalHull (fractionRow6.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev6_plane64 rev6_plane9 rev6_s1_ll rev6_s1_lr rev6_s1_ul rev6_s1_ur
    (by decide) rev6_s1_ll_mem rev6_s1_lr_mem rev6_s1_ul_mem rev6_s1_ur_mem p
    (hp _ rev6_plane64_mem) (hp _ rev6_plane9_mem) hx0 hx1
def rev6_s2_ll : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev6_s2_ll_mem : rev6_s2_ll.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane47 rev6_vertex3 rev6_vertex0 rev6_s2_ll
    rev6_vertex3_mem rev6_vertex0_mem (by decide)
def rev6_s2_lr : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev6_s2_lr_mem : rev6_s2_lr.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane47 rev6_vertex3 rev6_vertex0 rev6_s2_lr
    rev6_vertex3_mem rev6_vertex0_mem (by decide)
def rev6_s2_ul : FractionPoint := ⟨1478090653118879,6436683405200000,2727590407806825564641,11586963448453754000000⟩
theorem rev6_s2_ul_mem : rev6_s2_ul.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane9 rev6_vertex1 rev6_vertex0 rev6_s2_ul
    rev6_vertex1_mem rev6_vertex0_mem (by decide)
def rev6_s2_ur : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev6_s2_ur_mem : rev6_s2_ur.real ∈ rationalHull (fractionRow6.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow6 rev6_plane9 rev6_vertex1 rev6_vertex0 rev6_s2_ur
    rev6_vertex1_mem rev6_vertex0_mem (by decide)
theorem rev6_slab2 (p : Point) (hp : p∈IntegerCarrier rev6_planes)
    (hx0 : rev6_s2_ll.real.1≤p.1) (hx1 : p.1≤rev6_s2_lr.real.1) :
    p∈rationalHull (fractionRow6.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev6_plane47 rev6_plane9 rev6_s2_ll rev6_s2_lr rev6_s2_ul rev6_s2_ur
    (by decide) rev6_s2_ll_mem rev6_s2_lr_mem rev6_s2_ul_mem rev6_s2_ur_mem p
    (hp _ rev6_plane47_mem) (hp _ rev6_plane9_mem) hx0 hx1
theorem rev6_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev6_planes) : rev6_s0_ll.real.1≤p.1 := by
  have hc := rev6_plane8.combine_sound rev6_plane64 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev6_plane8_mem) (hp _ rev6_plane64_mem)
  exact (rev6_plane8.combine rev6_plane64 2129316000000 2139684000000).xBoundCheck_sound rev6_s0_ll.nx rev6_s0_ll.dx true (by decide) p hc
theorem rev6_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev6_planes) : p.1≤rev6_s2_lr.real.1 := by
  have hc := rev6_plane9.combine_sound rev6_plane47 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev6_plane9_mem) (hp _ rev6_plane47_mem)
  exact (rev6_plane9.combine rev6_plane47 1855520000000 1440116000000).xBoundCheck_sound rev6_s2_lr.nx rev6_s2_lr.dx false (by decide) p hc
theorem rev6_hull (p : Point) (hp : p∈IntegerCarrier rev6_planes) :
    p∈rationalHull (fractionRow6.map FractionPoint.rational) := by
  have hxlo := rev6_bound0_lo p hp
  have hxhi := rev6_bound0_hi p hp
  by_cases h0 : p.1≤rev6_s0_lr.real.1
  · exact rev6_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev6_s1_lr.real.1
  · exact rev6_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev6_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull6 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow6 := by
  rw [← fractionRow6_correct]
  exact rev6_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull6
