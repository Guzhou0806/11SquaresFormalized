import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev41_planes : List IntegerPlane := integerOverlayPlanes ![4,6,5,5]
def rev41_plane13 : IntegerPlane := ⟨2093220000000,1468788000000,1212544726896⟩
theorem rev41_plane13_mem : rev41_plane13 ∈ rev41_planes := by decide
def rev41_plane35 : IntegerPlane := ⟨(-2093220000000),1468788000000,256243273104⟩
theorem rev41_plane35_mem : rev41_plane35 ∈ rev41_planes := by decide
def rev41_plane46 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-1359544139484)⟩
theorem rev41_plane46_mem : rev41_plane46 ∈ rev41_planes := by decide
def rev41_vertex0 : FractionPoint := fractionRow41[0]!
theorem rev41_vertex0_mem : rev41_vertex0∈fractionRow41 := by decide
def rev41_vertex1 : FractionPoint := fractionRow41[1]!
theorem rev41_vertex1_mem : rev41_vertex1∈fractionRow41 := by decide
def rev41_vertex2 : FractionPoint := fractionRow41[2]!
theorem rev41_vertex2_mem : rev41_vertex2∈fractionRow41 := by decide
def rev41_s0_ll : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev41_s0_ll_mem : rev41_s0_ll.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane46 rev41_vertex2 rev41_vertex0 rev41_s0_ll
    rev41_vertex2_mem rev41_vertex0_mem (by decide)
def rev41_s0_lr : FractionPoint := ⟨3320491159,14536250000,15135847988765151,30522171140000000⟩
theorem rev41_s0_lr_mem : rev41_s0_lr.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane46 rev41_vertex2 rev41_vertex0 rev41_s0_lr
    rev41_vertex2_mem rev41_vertex0_mem (by decide)
def rev41_s0_ul : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev41_s0_ul_mem : rev41_s0_ul.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane35 rev41_vertex2 rev41_vertex1 rev41_s0_ul
    rev41_vertex2_mem rev41_vertex1_mem (by decide)
def rev41_s0_ur : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev41_s0_ur_mem : rev41_s0_ur.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane35 rev41_vertex2 rev41_vertex1 rev41_s0_ur
    rev41_vertex2_mem rev41_vertex1_mem (by decide)
theorem rev41_slab0 (p : Point) (hp : p∈IntegerCarrier rev41_planes)
    (hx0 : rev41_s0_ll.real.1≤p.1) (hx1 : p.1≤rev41_s0_lr.real.1) :
    p∈rationalHull (fractionRow41.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev41_plane46 rev41_plane35 rev41_s0_ll rev41_s0_lr rev41_s0_ul rev41_s0_ur
    (by decide) rev41_s0_ll_mem rev41_s0_lr_mem rev41_s0_ul_mem rev41_s0_ur_mem p
    (hp _ rev41_plane46_mem) (hp _ rev41_plane35_mem) hx0 hx1
def rev41_s1_ll : FractionPoint := ⟨3320491159,14536250000,15135847988765151,30522171140000000⟩
theorem rev41_s1_ll_mem : rev41_s1_ll.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane46 rev41_vertex2 rev41_vertex0 rev41_s1_ll
    rev41_vertex2_mem rev41_vertex0_mem (by decide)
def rev41_s1_lr : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev41_s1_lr_mem : rev41_s1_lr.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane46 rev41_vertex2 rev41_vertex0 rev41_s1_lr
    rev41_vertex2_mem rev41_vertex0_mem (by decide)
def rev41_s1_ul : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev41_s1_ul_mem : rev41_s1_ul.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane13 rev41_vertex1 rev41_vertex0 rev41_s1_ul
    rev41_vertex1_mem rev41_vertex0_mem (by decide)
def rev41_s1_ur : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev41_s1_ur_mem : rev41_s1_ur.real ∈ rationalHull (fractionRow41.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow41 rev41_plane13 rev41_vertex1 rev41_vertex0 rev41_s1_ur
    rev41_vertex1_mem rev41_vertex0_mem (by decide)
theorem rev41_slab1 (p : Point) (hp : p∈IntegerCarrier rev41_planes)
    (hx0 : rev41_s1_ll.real.1≤p.1) (hx1 : p.1≤rev41_s1_lr.real.1) :
    p∈rationalHull (fractionRow41.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev41_plane46 rev41_plane13 rev41_s1_ll rev41_s1_lr rev41_s1_ul rev41_s1_ur
    (by decide) rev41_s1_ll_mem rev41_s1_lr_mem rev41_s1_ul_mem rev41_s1_ur_mem p
    (hp _ rev41_plane46_mem) (hp _ rev41_plane13_mem) hx0 hx1
theorem rev41_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev41_planes) : rev41_s0_ll.real.1≤p.1 := by
  have hc := rev41_plane35.combine_sound rev41_plane46 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev41_plane35_mem) (hp _ rev41_plane46_mem)
  exact (rev41_plane35.combine rev41_plane46 2099728000000 1468788000000).xBoundCheck_sound rev41_s0_ll.nx rev41_s0_ll.dx true (by decide) p hc
theorem rev41_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev41_planes) : p.1≤rev41_s1_lr.real.1 := by
  have hc := rev41_plane13.combine_sound rev41_plane46 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev41_plane13_mem) (hp _ rev41_plane46_mem)
  exact (rev41_plane13.combine rev41_plane46 2099728000000 1468788000000).xBoundCheck_sound rev41_s1_lr.nx rev41_s1_lr.dx false (by decide) p hc
theorem rev41_hull (p : Point) (hp : p∈IntegerCarrier rev41_planes) :
    p∈rationalHull (fractionRow41.map FractionPoint.rational) := by
  have hxlo := rev41_bound0_lo p hp
  have hxhi := rev41_bound0_hi p hp
  by_cases h0 : p.1≤rev41_s0_lr.real.1
  · exact rev41_slab0 p hp hxlo h0
  exact rev41_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull41 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,6,5,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow41 := by
  rw [← fractionRow41_correct]
  exact rev41_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull41
