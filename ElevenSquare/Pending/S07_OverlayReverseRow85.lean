import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev85_planes : List IntegerPlane := integerOverlayPlanes ![6,9,6,9]
def rev85_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev85_plane13_mem : rev85_plane13 ∈ rev85_planes := by decide
def rev85_plane29 : IntegerPlane := ⟨(-51300000000),(-2168356000000),(-1004834835544)⟩
theorem rev85_plane29_mem : rev85_plane29 ∈ rev85_planes := by decide
def rev85_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev85_plane30_mem : rev85_plane30 ∈ rev85_planes := by decide
def rev85_plane53 : IntegerPlane := ⟨1343640000000,2164112000000,1753876000000⟩
theorem rev85_plane53_mem : rev85_plane53 ∈ rev85_planes := by decide
def rev85_plane54 : IntegerPlane := ⟨2168356000000,51300000000,1214821164456⟩
theorem rev85_plane54_mem : rev85_plane54 ∈ rev85_planes := by decide
def rev85_vertex0 : FractionPoint := fractionRow85[0]!
theorem rev85_vertex0_mem : rev85_vertex0∈fractionRow85 := by decide
def rev85_vertex1 : FractionPoint := fractionRow85[1]!
theorem rev85_vertex1_mem : rev85_vertex1∈fractionRow85 := by decide
def rev85_vertex2 : FractionPoint := fractionRow85[2]!
theorem rev85_vertex2_mem : rev85_vertex2∈fractionRow85 := by decide
def rev85_vertex3 : FractionPoint := fractionRow85[3]!
theorem rev85_vertex3_mem : rev85_vertex3∈fractionRow85 := by decide
def rev85_s0_ll : FractionPoint := ⟨1,2,1,2⟩
theorem rev85_s0_ll_mem : rev85_s0_ll.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane30 rev85_vertex0 rev85_vertex1 rev85_s0_ll
    rev85_vertex0_mem rev85_vertex1_mem (by decide)
def rev85_s0_lr : FractionPoint := ⟨403436064050273,760466530900000,857155134382729,1901166327250000⟩
theorem rev85_s0_lr_mem : rev85_s0_lr.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane30 rev85_vertex0 rev85_vertex1 rev85_s0_lr
    rev85_vertex0_mem rev85_vertex1_mem (by decide)
def rev85_s0_ul : FractionPoint := ⟨1,2,1,2⟩
theorem rev85_s0_ul_mem : rev85_s0_ul.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane53 rev85_vertex0 rev85_vertex3 rev85_s0_ul
    rev85_vertex0_mem rev85_vertex3_mem (by decide)
def rev85_s0_ur : FractionPoint := ⟨403436064050273,760466530900000,19792279106206489657,41143368627976520000⟩
theorem rev85_s0_ur_mem : rev85_s0_ur.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane53 rev85_vertex0 rev85_vertex3 rev85_s0_ur
    rev85_vertex0_mem rev85_vertex3_mem (by decide)
theorem rev85_slab0 (p : Point) (hp : p∈IntegerCarrier rev85_planes)
    (hx0 : rev85_s0_ll.real.1≤p.1) (hx1 : p.1≤rev85_s0_lr.real.1) :
    p∈rationalHull (fractionRow85.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev85_plane30 rev85_plane53 rev85_s0_ll rev85_s0_lr rev85_s0_ul rev85_s0_ur
    (by decide) rev85_s0_ll_mem rev85_s0_lr_mem rev85_s0_ul_mem rev85_s0_ur_mem p
    (hp _ rev85_plane30_mem) (hp _ rev85_plane53_mem) hx0 hx1
def rev85_s1_ll : FractionPoint := ⟨403436064050273,760466530900000,857155134382729,1901166327250000⟩
theorem rev85_s1_ll_mem : rev85_s1_ll.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane29 rev85_vertex1 rev85_vertex2 rev85_s1_ll
    rev85_vertex1_mem rev85_vertex2_mem (by decide)
def rev85_s1_lr : FractionPoint := ⟨1044011192867271,1901166327250000,48863167883946137723,108484352965539500000⟩
theorem rev85_s1_lr_mem : rev85_s1_lr.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane29 rev85_vertex1 rev85_vertex2 rev85_s1_lr
    rev85_vertex1_mem rev85_vertex2_mem (by decide)
def rev85_s1_ul : FractionPoint := ⟨403436064050273,760466530900000,19792279106206489657,41143368627976520000⟩
theorem rev85_s1_ul_mem : rev85_s1_ul.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane53 rev85_vertex0 rev85_vertex3 rev85_s1_ul
    rev85_vertex0_mem rev85_vertex3_mem (by decide)
def rev85_s1_ur : FractionPoint := ⟨1044011192867271,1901166327250000,357030466849727,760466530900000⟩
theorem rev85_s1_ur_mem : rev85_s1_ur.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane53 rev85_vertex0 rev85_vertex3 rev85_s1_ur
    rev85_vertex0_mem rev85_vertex3_mem (by decide)
theorem rev85_slab1 (p : Point) (hp : p∈IntegerCarrier rev85_planes)
    (hx0 : rev85_s1_ll.real.1≤p.1) (hx1 : p.1≤rev85_s1_lr.real.1) :
    p∈rationalHull (fractionRow85.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev85_plane29 rev85_plane53 rev85_s1_ll rev85_s1_lr rev85_s1_ul rev85_s1_ur
    (by decide) rev85_s1_ll_mem rev85_s1_lr_mem rev85_s1_ul_mem rev85_s1_ur_mem p
    (hp _ rev85_plane29_mem) (hp _ rev85_plane53_mem) hx0 hx1
def rev85_s2_ll : FractionPoint := ⟨1044011192867271,1901166327250000,48863167883946137723,108484352965539500000⟩
theorem rev85_s2_ll_mem : rev85_s2_ll.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane29 rev85_vertex1 rev85_vertex2 rev85_s2_ll
    rev85_vertex1_mem rev85_vertex2_mem (by decide)
def rev85_s2_lr : FractionPoint := ⟨7654744503,13928000000,6273255497,13928000000⟩
theorem rev85_s2_lr_mem : rev85_s2_lr.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane29 rev85_vertex1 rev85_vertex2 rev85_s2_lr
    rev85_vertex1_mem rev85_vertex2_mem (by decide)
def rev85_s2_ul : FractionPoint := ⟨1044011192867271,1901166327250000,357030466849727,760466530900000⟩
theorem rev85_s2_ul_mem : rev85_s2_ul.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane54 rev85_vertex3 rev85_vertex2 rev85_s2_ul
    rev85_vertex3_mem rev85_vertex2_mem (by decide)
def rev85_s2_ur : FractionPoint := ⟨7654744503,13928000000,6273255497,13928000000⟩
theorem rev85_s2_ur_mem : rev85_s2_ur.real ∈ rationalHull (fractionRow85.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow85 rev85_plane54 rev85_vertex3 rev85_vertex2 rev85_s2_ur
    rev85_vertex3_mem rev85_vertex2_mem (by decide)
theorem rev85_slab2 (p : Point) (hp : p∈IntegerCarrier rev85_planes)
    (hx0 : rev85_s2_ll.real.1≤p.1) (hx1 : p.1≤rev85_s2_lr.real.1) :
    p∈rationalHull (fractionRow85.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev85_plane29 rev85_plane54 rev85_s2_ll rev85_s2_lr rev85_s2_ul rev85_s2_ur
    (by decide) rev85_s2_ll_mem rev85_s2_lr_mem rev85_s2_ul_mem rev85_s2_ur_mem p
    (hp _ rev85_plane29_mem) (hp _ rev85_plane54_mem) hx0 hx1
theorem rev85_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev85_planes) : rev85_s0_ll.real.1≤p.1 := by
  have hc := rev85_plane13.combine_sound rev85_plane30 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev85_plane13_mem) (hp _ rev85_plane30_mem)
  exact (rev85_plane13.combine rev85_plane30 1343640000000 1343640000000).xBoundCheck_sound rev85_s0_ll.nx rev85_s0_ll.dx true (by decide) p hc
theorem rev85_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev85_planes) : p.1≤rev85_s2_lr.real.1 := by
  have hc := rev85_plane29.combine_sound rev85_plane54 51300000000 2168356000000 (by decide) (by decide) p
    (hp _ rev85_plane29_mem) (hp _ rev85_plane54_mem)
  exact (rev85_plane29.combine rev85_plane54 51300000000 2168356000000).xBoundCheck_sound rev85_s2_lr.nx rev85_s2_lr.dx false (by decide) p hc
theorem rev85_hull (p : Point) (hp : p∈IntegerCarrier rev85_planes) :
    p∈rationalHull (fractionRow85.map FractionPoint.rational) := by
  have hxlo := rev85_bound0_lo p hp
  have hxhi := rev85_bound0_hi p hp
  by_cases h0 : p.1≤rev85_s0_lr.real.1
  · exact rev85_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev85_s1_lr.real.1
  · exact rev85_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev85_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull85 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow85 := by
  rw [← fractionRow85_correct]
  exact rev85_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull85
