import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev67_planes : List IntegerPlane := integerOverlayPlanes ![5,5,11,9]
def rev67_plane6 : IntegerPlane := ⟨2099728000000,(-1393416000000),740183860516⟩
theorem rev67_plane6_mem : rev67_plane6 ∈ rev67_planes := by decide
def rev67_plane50 : IntegerPlane := ⟨(-1468788000000),2093220000000,(-256243273104)⟩
theorem rev67_plane50_mem : rev67_plane50 ∈ rev67_planes := by decide
def rev67_plane68 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-1212544726896)⟩
theorem rev67_plane68_mem : rev67_plane68 ∈ rev67_planes := by decide
def rev67_vertex0 : FractionPoint := fractionRow67[0]!
theorem rev67_vertex0_mem : rev67_vertex0∈fractionRow67 := by decide
def rev67_vertex1 : FractionPoint := fractionRow67[1]!
theorem rev67_vertex1_mem : rev67_vertex1∈fractionRow67 := by decide
def rev67_vertex2 : FractionPoint := fractionRow67[2]!
theorem rev67_vertex2_mem : rev67_vertex2∈fractionRow67 := by decide
def rev67_s0_ll : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev67_s0_ll_mem : rev67_s0_ll.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane68 rev67_vertex2 rev67_vertex0 rev67_s0_ll
    rev67_vertex2_mem rev67_vertex0_mem (by decide)
def rev67_s0_lr : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev67_s0_lr_mem : rev67_s0_lr.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane68 rev67_vertex2 rev67_vertex0 rev67_s0_lr
    rev67_vertex2_mem rev67_vertex0_mem (by decide)
def rev67_s0_ul : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev67_s0_ul_mem : rev67_s0_ul.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane50 rev67_vertex2 rev67_vertex1 rev67_s0_ul
    rev67_vertex2_mem rev67_vertex1_mem (by decide)
def rev67_s0_ur : FractionPoint := ⟨22492686692234849,44734898222000000,1797830963244554114327,7803331971354570000000⟩
theorem rev67_s0_ur_mem : rev67_s0_ur.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane50 rev67_vertex2 rev67_vertex1 rev67_s0_ur
    rev67_vertex2_mem rev67_vertex1_mem (by decide)
theorem rev67_slab0 (p : Point) (hp : p∈IntegerCarrier rev67_planes)
    (hx0 : rev67_s0_ll.real.1≤p.1) (hx1 : p.1≤rev67_s0_lr.real.1) :
    p∈rationalHull (fractionRow67.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev67_plane68 rev67_plane50 rev67_s0_ll rev67_s0_lr rev67_s0_ul rev67_s0_ur
    (by decide) rev67_s0_ll_mem rev67_s0_lr_mem rev67_s0_ul_mem rev67_s0_ur_mem p
    (hp _ rev67_plane68_mem) (hp _ rev67_plane50_mem) hx0 hx1
def rev67_s1_ll : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev67_s1_ll_mem : rev67_s1_ll.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane6 rev67_vertex0 rev67_vertex1 rev67_s1_ll
    rev67_vertex0_mem rev67_vertex1_mem (by decide)
def rev67_s1_lr : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev67_s1_lr_mem : rev67_s1_lr.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane6 rev67_vertex0 rev67_vertex1 rev67_s1_lr
    rev67_vertex0_mem rev67_vertex1_mem (by decide)
def rev67_s1_ul : FractionPoint := ⟨22492686692234849,44734898222000000,1797830963244554114327,7803331971354570000000⟩
theorem rev67_s1_ul_mem : rev67_s1_ul.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane50 rev67_vertex2 rev67_vertex1 rev67_s1_ul
    rev67_vertex2_mem rev67_vertex1_mem (by decide)
def rev67_s1_ur : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev67_s1_ur_mem : rev67_s1_ur.real ∈ rationalHull (fractionRow67.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow67 rev67_plane50 rev67_vertex2 rev67_vertex1 rev67_s1_ur
    rev67_vertex2_mem rev67_vertex1_mem (by decide)
theorem rev67_slab1 (p : Point) (hp : p∈IntegerCarrier rev67_planes)
    (hx0 : rev67_s1_ll.real.1≤p.1) (hx1 : p.1≤rev67_s1_lr.real.1) :
    p∈rationalHull (fractionRow67.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev67_plane6 rev67_plane50 rev67_s1_ll rev67_s1_lr rev67_s1_ul rev67_s1_ur
    (by decide) rev67_s1_ll_mem rev67_s1_lr_mem rev67_s1_ul_mem rev67_s1_ur_mem p
    (hp _ rev67_plane6_mem) (hp _ rev67_plane50_mem) hx0 hx1
theorem rev67_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev67_planes) : rev67_s0_ll.real.1≤p.1 := by
  have hc := rev67_plane50.combine_sound rev67_plane68 2093220000000 2093220000000 (by decide) (by decide) p
    (hp _ rev67_plane50_mem) (hp _ rev67_plane68_mem)
  exact (rev67_plane50.combine rev67_plane68 2093220000000 2093220000000).xBoundCheck_sound rev67_s0_ll.nx rev67_s0_ll.dx true (by decide) p hc
theorem rev67_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev67_planes) : p.1≤rev67_s1_lr.real.1 := by
  have hc := rev67_plane6.combine_sound rev67_plane50 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev67_plane6_mem) (hp _ rev67_plane50_mem)
  exact (rev67_plane6.combine rev67_plane50 2093220000000 1393416000000).xBoundCheck_sound rev67_s1_lr.nx rev67_s1_lr.dx false (by decide) p hc
theorem rev67_hull (p : Point) (hp : p∈IntegerCarrier rev67_planes) :
    p∈rationalHull (fractionRow67.map FractionPoint.rational) := by
  have hxlo := rev67_bound0_lo p hp
  have hxhi := rev67_bound0_hi p hp
  by_cases h0 : p.1≤rev67_s0_lr.real.1
  · exact rev67_slab0 p hp hxlo h0
  exact rev67_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull67 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,5,11,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow67 := by
  rw [← fractionRow67_correct]
  exact rev67_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull67
