import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev58_planes : List IntegerPlane := integerOverlayPlanes ![5,2,7,0]
def rev58_plane4 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-827972119784)⟩
theorem rev58_plane4_mem : rev58_plane4 ∈ rev58_planes := by decide
def rev58_plane27 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-499376240400)⟩
theorem rev58_plane27_mem : rev58_plane27 ∈ rev58_planes := by decide
def rev58_plane68 : IntegerPlane := ⟨2139684000000,(-15204000000),568962228432⟩
theorem rev58_plane68_mem : rev58_plane68 ∈ rev58_planes := by decide
def rev58_plane69 : IntegerPlane := ⟨1440116000000,2129316000000,827972119784⟩
theorem rev58_plane69_mem : rev58_plane69 ∈ rev58_planes := by decide
def rev58_vertex0 : FractionPoint := fractionRow58[0]!
theorem rev58_vertex0_mem : rev58_vertex0∈fractionRow58 := by decide
def rev58_vertex1 : FractionPoint := fractionRow58[1]!
theorem rev58_vertex1_mem : rev58_vertex1∈fractionRow58 := by decide
def rev58_vertex2 : FractionPoint := fractionRow58[2]!
theorem rev58_vertex2_mem : rev58_vertex2∈fractionRow58 := by decide
def rev58_vertex3 : FractionPoint := fractionRow58[3]!
theorem rev58_vertex3_mem : rev58_vertex3∈fractionRow58 := by decide
def rev58_s0_ll : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev58_s0_ll_mem : rev58_s0_ll.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane27 rev58_vertex3 rev58_vertex0 rev58_s0_ll
    rev58_vertex3_mem rev58_vertex0_mem (by decide)
def rev58_s0_lr : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev58_s0_lr_mem : rev58_s0_lr.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane27 rev58_vertex3 rev58_vertex0 rev58_s0_lr
    rev58_vertex3_mem rev58_vertex0_mem (by decide)
def rev58_s0_ul : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev58_s0_ul_mem : rev58_s0_ul.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane69 rev58_vertex3 rev58_vertex2 rev58_s0_ul
    rev58_vertex3_mem rev58_vertex2_mem (by decide)
def rev58_s0_ur : FractionPoint := ⟨7515963822126429,32183417026000000,791155613062213630831,3426433240406710800000⟩
theorem rev58_s0_ur_mem : rev58_s0_ur.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane69 rev58_vertex3 rev58_vertex2 rev58_s0_ur
    rev58_vertex3_mem rev58_vertex2_mem (by decide)
theorem rev58_slab0 (p : Point) (hp : p∈IntegerCarrier rev58_planes)
    (hx0 : rev58_s0_ll.real.1≤p.1) (hx1 : p.1≤rev58_s0_lr.real.1) :
    p∈rationalHull (fractionRow58.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev58_plane27 rev58_plane69 rev58_s0_ll rev58_s0_lr rev58_s0_ul rev58_s0_ur
    (by decide) rev58_s0_ll_mem rev58_s0_lr_mem rev58_s0_ul_mem rev58_s0_ur_mem p
    (hp _ rev58_plane27_mem) (hp _ rev58_plane69_mem) hx0 hx1
def rev58_s1_ll : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev58_s1_ll_mem : rev58_s1_ll.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane4 rev58_vertex0 rev58_vertex1 rev58_s1_ll
    rev58_vertex0_mem rev58_vertex1_mem (by decide)
def rev58_s1_lr : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev58_s1_lr_mem : rev58_s1_lr.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane4 rev58_vertex0 rev58_vertex1 rev58_s1_lr
    rev58_vertex0_mem rev58_vertex1_mem (by decide)
def rev58_s1_ul : FractionPoint := ⟨7515963822126429,32183417026000000,791155613062213630831,3426433240406710800000⟩
theorem rev58_s1_ul_mem : rev58_s1_ul.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane69 rev58_vertex3 rev58_vertex2 rev58_s1_ul
    rev58_vertex3_mem rev58_vertex2_mem (by decide)
def rev58_s1_ur : FractionPoint := ⟨8666251006976813,32435075873000000,1197910982563272028427,5755377168132739000000⟩
theorem rev58_s1_ur_mem : rev58_s1_ur.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane69 rev58_vertex3 rev58_vertex2 rev58_s1_ur
    rev58_vertex3_mem rev58_vertex2_mem (by decide)
theorem rev58_slab1 (p : Point) (hp : p∈IntegerCarrier rev58_planes)
    (hx0 : rev58_s1_ll.real.1≤p.1) (hx1 : p.1≤rev58_s1_lr.real.1) :
    p∈rationalHull (fractionRow58.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev58_plane4 rev58_plane69 rev58_s1_ll rev58_s1_lr rev58_s1_ul rev58_s1_ur
    (by decide) rev58_s1_ll_mem rev58_s1_lr_mem rev58_s1_ul_mem rev58_s1_ur_mem p
    (hp _ rev58_plane4_mem) (hp _ rev58_plane69_mem) hx0 hx1
def rev58_s2_ll : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev58_s2_ll_mem : rev58_s2_ll.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane68 rev58_vertex1 rev58_vertex2 rev58_s2_ll
    rev58_vertex1_mem rev58_vertex2_mem (by decide)
def rev58_s2_lr : FractionPoint := ⟨79198296098933,296192993000000,431262268381943,2073350951000000⟩
theorem rev58_s2_lr_mem : rev58_s2_lr.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane68 rev58_vertex1 rev58_vertex2 rev58_s2_lr
    rev58_vertex1_mem rev58_vertex2_mem (by decide)
def rev58_s2_ul : FractionPoint := ⟨8666251006976813,32435075873000000,1197910982563272028427,5755377168132739000000⟩
theorem rev58_s2_ul_mem : rev58_s2_ul.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane69 rev58_vertex3 rev58_vertex2 rev58_s2_ul
    rev58_vertex3_mem rev58_vertex2_mem (by decide)
def rev58_s2_ur : FractionPoint := ⟨79198296098933,296192993000000,431262268381943,2073350951000000⟩
theorem rev58_s2_ur_mem : rev58_s2_ur.real ∈ rationalHull (fractionRow58.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow58 rev58_plane69 rev58_vertex3 rev58_vertex2 rev58_s2_ur
    rev58_vertex3_mem rev58_vertex2_mem (by decide)
theorem rev58_slab2 (p : Point) (hp : p∈IntegerCarrier rev58_planes)
    (hx0 : rev58_s2_ll.real.1≤p.1) (hx1 : p.1≤rev58_s2_lr.real.1) :
    p∈rationalHull (fractionRow58.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev58_plane68 rev58_plane69 rev58_s2_ll rev58_s2_lr rev58_s2_ul rev58_s2_ur
    (by decide) rev58_s2_ll_mem rev58_s2_lr_mem rev58_s2_ul_mem rev58_s2_ur_mem p
    (hp _ rev58_plane68_mem) (hp _ rev58_plane69_mem) hx0 hx1
theorem rev58_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev58_planes) : rev58_s0_ll.real.1≤p.1 := by
  have hc := rev58_plane27.combine_sound rev58_plane69 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev58_plane27_mem) (hp _ rev58_plane69_mem)
  exact (rev58_plane27.combine rev58_plane69 2129316000000 287616000000).xBoundCheck_sound rev58_s0_ll.nx rev58_s0_ll.dx true (by decide) p hc
theorem rev58_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev58_planes) : p.1≤rev58_s2_lr.real.1 := by
  have hc := rev58_plane68.combine_sound rev58_plane69 2129316000000 15204000000 (by decide) (by decide) p
    (hp _ rev58_plane68_mem) (hp _ rev58_plane69_mem)
  exact (rev58_plane68.combine rev58_plane69 2129316000000 15204000000).xBoundCheck_sound rev58_s2_lr.nx rev58_s2_lr.dx false (by decide) p hc
theorem rev58_hull (p : Point) (hp : p∈IntegerCarrier rev58_planes) :
    p∈rationalHull (fractionRow58.map FractionPoint.rational) := by
  have hxlo := rev58_bound0_lo p hp
  have hxhi := rev58_bound0_hi p hp
  by_cases h0 : p.1≤rev58_s0_lr.real.1
  · exact rev58_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev58_s1_lr.real.1
  · exact rev58_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev58_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull58 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow58 := by
  rw [← fractionRow58_correct]
  exact rev58_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull58
