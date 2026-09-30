import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev64_planes : List IntegerPlane := integerOverlayPlanes ![5,5,6,4]
def rev64_plane26 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-1359544139484)⟩
theorem rev64_plane26_mem : rev64_plane26 ∈ rev64_planes := by decide
def rev64_plane55 : IntegerPlane := ⟨1468788000000,(-2093220000000),256243273104⟩
theorem rev64_plane55_mem : rev64_plane55 ∈ rev64_planes := by decide
def rev64_plane73 : IntegerPlane := ⟨1468788000000,2093220000000,1212544726896⟩
theorem rev64_plane73_mem : rev64_plane73 ∈ rev64_planes := by decide
def rev64_vertex0 : FractionPoint := fractionRow64[0]!
theorem rev64_vertex0_mem : rev64_vertex0∈fractionRow64 := by decide
def rev64_vertex1 : FractionPoint := fractionRow64[1]!
theorem rev64_vertex1_mem : rev64_vertex1∈fractionRow64 := by decide
def rev64_vertex2 : FractionPoint := fractionRow64[2]!
theorem rev64_vertex2_mem : rev64_vertex2∈fractionRow64 := by decide
def rev64_s0_ll : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev64_s0_ll_mem : rev64_s0_ll.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane26 rev64_vertex0 rev64_vertex1 rev64_s0_ll
    rev64_vertex0_mem rev64_vertex1_mem (by decide)
def rev64_s0_lr : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev64_s0_lr_mem : rev64_s0_lr.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane26 rev64_vertex0 rev64_vertex1 rev64_s0_lr
    rev64_vertex0_mem rev64_vertex1_mem (by decide)
def rev64_s0_ul : FractionPoint := ⟨8029484447765151,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev64_s0_ul_mem : rev64_s0_ul.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane73 rev64_vertex0 rev64_vertex2 rev64_s0_ul
    rev64_vertex0_mem rev64_vertex2_mem (by decide)
def rev64_s0_ur : FractionPoint := ⟨22242211529765151,44734898222000000,1797830963244554114327,7803331971354570000000⟩
theorem rev64_s0_ur_mem : rev64_s0_ur.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane73 rev64_vertex0 rev64_vertex2 rev64_s0_ur
    rev64_vertex0_mem rev64_vertex2_mem (by decide)
theorem rev64_slab0 (p : Point) (hp : p∈IntegerCarrier rev64_planes)
    (hx0 : rev64_s0_ll.real.1≤p.1) (hx1 : p.1≤rev64_s0_lr.real.1) :
    p∈rationalHull (fractionRow64.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev64_plane26 rev64_plane73 rev64_s0_ll rev64_s0_lr rev64_s0_ul rev64_s0_ur
    (by decide) rev64_s0_ll_mem rev64_s0_lr_mem rev64_s0_ul_mem rev64_s0_ur_mem p
    (hp _ rev64_plane26_mem) (hp _ rev64_plane73_mem) hx0 hx1
def rev64_s1_ll : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev64_s1_ll_mem : rev64_s1_ll.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane55 rev64_vertex1 rev64_vertex2 rev64_s1_ll
    rev64_vertex1_mem rev64_vertex2_mem (by decide)
def rev64_s1_lr : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev64_s1_lr_mem : rev64_s1_lr.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane55 rev64_vertex1 rev64_vertex2 rev64_s1_lr
    rev64_vertex1_mem rev64_vertex2_mem (by decide)
def rev64_s1_ul : FractionPoint := ⟨22242211529765151,44734898222000000,1797830963244554114327,7803331971354570000000⟩
theorem rev64_s1_ul_mem : rev64_s1_ul.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane73 rev64_vertex0 rev64_vertex2 rev64_s1_ul
    rev64_vertex0_mem rev64_vertex2_mem (by decide)
def rev64_s1_ur : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev64_s1_ur_mem : rev64_s1_ur.real ∈ rationalHull (fractionRow64.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow64 rev64_plane73 rev64_vertex0 rev64_vertex2 rev64_s1_ur
    rev64_vertex0_mem rev64_vertex2_mem (by decide)
theorem rev64_slab1 (p : Point) (hp : p∈IntegerCarrier rev64_planes)
    (hx0 : rev64_s1_ll.real.1≤p.1) (hx1 : p.1≤rev64_s1_lr.real.1) :
    p∈rationalHull (fractionRow64.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev64_plane55 rev64_plane73 rev64_s1_ll rev64_s1_lr rev64_s1_ul rev64_s1_ur
    (by decide) rev64_s1_ll_mem rev64_s1_lr_mem rev64_s1_ul_mem rev64_s1_ur_mem p
    (hp _ rev64_plane55_mem) (hp _ rev64_plane73_mem) hx0 hx1
theorem rev64_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev64_planes) : rev64_s0_ll.real.1≤p.1 := by
  have hc := rev64_plane26.combine_sound rev64_plane73 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev64_plane26_mem) (hp _ rev64_plane73_mem)
  exact (rev64_plane26.combine rev64_plane73 2093220000000 1393416000000).xBoundCheck_sound rev64_s0_ll.nx rev64_s0_ll.dx true (by decide) p hc
theorem rev64_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev64_planes) : p.1≤rev64_s1_lr.real.1 := by
  have hc := rev64_plane55.combine_sound rev64_plane73 2093220000000 2093220000000 (by decide) (by decide) p
    (hp _ rev64_plane55_mem) (hp _ rev64_plane73_mem)
  exact (rev64_plane55.combine rev64_plane73 2093220000000 2093220000000).xBoundCheck_sound rev64_s1_lr.nx rev64_s1_lr.dx false (by decide) p hc
theorem rev64_hull (p : Point) (hp : p∈IntegerCarrier rev64_planes) :
    p∈rationalHull (fractionRow64.map FractionPoint.rational) := by
  have hxlo := rev64_bound0_lo p hp
  have hxhi := rev64_bound0_hi p hp
  by_cases h0 : p.1≤rev64_s0_lr.real.1
  · exact rev64_slab0 p hp hxlo h0
  exact rev64_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull64 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,5,6,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow64 := by
  rw [← fractionRow64_correct]
  exact rev64_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull64
