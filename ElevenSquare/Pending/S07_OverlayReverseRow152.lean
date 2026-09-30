import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev152_planes : List IntegerPlane := integerOverlayPlanes ![10,10,4,6]
def rev152_plane17 : IntegerPlane := ⟨(-2099728000000),1393416000000,33871860516⟩
theorem rev152_plane17_mem : rev152_plane17 ∈ rev152_planes := by decide
def rev152_plane53 : IntegerPlane := ⟨1468788000000,(-2093220000000),(-880675273104)⟩
theorem rev152_plane53_mem : rev152_plane53 ∈ rev152_planes := by decide
def rev152_plane75 : IntegerPlane := ⟨1468788000000,2093220000000,2349463273104⟩
theorem rev152_plane75_mem : rev152_plane75 ∈ rev152_planes := by decide
def rev152_vertex0 : FractionPoint := fractionRow152[0]!
theorem rev152_vertex0_mem : rev152_vertex0∈fractionRow152 := by decide
def rev152_vertex1 : FractionPoint := fractionRow152[1]!
theorem rev152_vertex1_mem : rev152_vertex1∈fractionRow152 := by decide
def rev152_vertex2 : FractionPoint := fractionRow152[2]!
theorem rev152_vertex2_mem : rev152_vertex2∈fractionRow152 := by decide
def rev152_s0_ll : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev152_s0_ll_mem : rev152_s0_ll.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane53 rev152_vertex1 rev152_vertex2 rev152_s0_ll
    rev152_vertex1_mem rev152_vertex2_mem (by decide)
def rev152_s0_lr : FractionPoint := ⟨22242211529765151,44734898222000000,6005501008110015885673,7803331971354570000000⟩
theorem rev152_s0_lr_mem : rev152_s0_lr.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane53 rev152_vertex1 rev152_vertex2 rev152_s0_lr
    rev152_vertex1_mem rev152_vertex2_mem (by decide)
def rev152_s0_ul : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev152_s0_ul_mem : rev152_s0_ul.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane17 rev152_vertex1 rev152_vertex0 rev152_s0_ul
    rev152_vertex1_mem rev152_vertex0_mem (by decide)
def rev152_s0_ur : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev152_s0_ur_mem : rev152_s0_ur.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane17 rev152_vertex1 rev152_vertex0 rev152_s0_ur
    rev152_vertex1_mem rev152_vertex0_mem (by decide)
theorem rev152_slab0 (p : Point) (hp : p∈IntegerCarrier rev152_planes)
    (hx0 : rev152_s0_ll.real.1≤p.1) (hx1 : p.1≤rev152_s0_lr.real.1) :
    p∈rationalHull (fractionRow152.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev152_plane53 rev152_plane17 rev152_s0_ll rev152_s0_lr rev152_s0_ul rev152_s0_ur
    (by decide) rev152_s0_ll_mem rev152_s0_lr_mem rev152_s0_ul_mem rev152_s0_ur_mem p
    (hp _ rev152_plane53_mem) (hp _ rev152_plane17_mem) hx0 hx1
def rev152_s1_ll : FractionPoint := ⟨22242211529765151,44734898222000000,6005501008110015885673,7803331971354570000000⟩
theorem rev152_s1_ll_mem : rev152_s1_ll.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane53 rev152_vertex1 rev152_vertex2 rev152_s1_ll
    rev152_vertex1_mem rev152_vertex2_mem (by decide)
def rev152_s1_lr : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev152_s1_lr_mem : rev152_s1_lr.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane53 rev152_vertex1 rev152_vertex2 rev152_s1_lr
    rev152_vertex1_mem rev152_vertex2_mem (by decide)
def rev152_s1_ul : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev152_s1_ul_mem : rev152_s1_ul.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane75 rev152_vertex0 rev152_vertex2 rev152_s1_ul
    rev152_vertex0_mem rev152_vertex2_mem (by decide)
def rev152_s1_ur : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev152_s1_ur_mem : rev152_s1_ur.real ∈ rationalHull (fractionRow152.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow152 rev152_plane75 rev152_vertex0 rev152_vertex2 rev152_s1_ur
    rev152_vertex0_mem rev152_vertex2_mem (by decide)
theorem rev152_slab1 (p : Point) (hp : p∈IntegerCarrier rev152_planes)
    (hx0 : rev152_s1_ll.real.1≤p.1) (hx1 : p.1≤rev152_s1_lr.real.1) :
    p∈rationalHull (fractionRow152.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev152_plane53 rev152_plane75 rev152_s1_ll rev152_s1_lr rev152_s1_ul rev152_s1_ur
    (by decide) rev152_s1_ll_mem rev152_s1_lr_mem rev152_s1_ul_mem rev152_s1_ur_mem p
    (hp _ rev152_plane53_mem) (hp _ rev152_plane75_mem) hx0 hx1
theorem rev152_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev152_planes) : rev152_s0_ll.real.1≤p.1 := by
  have hc := rev152_plane17.combine_sound rev152_plane53 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev152_plane17_mem) (hp _ rev152_plane53_mem)
  exact (rev152_plane17.combine rev152_plane53 2093220000000 1393416000000).xBoundCheck_sound rev152_s0_ll.nx rev152_s0_ll.dx true (by decide) p hc
theorem rev152_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev152_planes) : p.1≤rev152_s1_lr.real.1 := by
  have hc := rev152_plane53.combine_sound rev152_plane75 2093220000000 2093220000000 (by decide) (by decide) p
    (hp _ rev152_plane53_mem) (hp _ rev152_plane75_mem)
  exact (rev152_plane53.combine rev152_plane75 2093220000000 2093220000000).xBoundCheck_sound rev152_s1_lr.nx rev152_s1_lr.dx false (by decide) p hc
theorem rev152_hull (p : Point) (hp : p∈IntegerCarrier rev152_planes) :
    p∈rationalHull (fractionRow152.map FractionPoint.rational) := by
  have hxlo := rev152_bound0_lo p hp
  have hxhi := rev152_bound0_hi p hp
  by_cases h0 : p.1≤rev152_s0_lr.real.1
  · exact rev152_slab0 p hp hxlo h0
  exact rev152_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull152 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,10,4,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow152 := by
  rw [← fractionRow152_correct]
  exact rev152_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull152
