import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev153_planes : List IntegerPlane := integerOverlayPlanes ![10,10,4,11]
def rev153_plane17 : IntegerPlane := ⟨(-2099728000000),1393416000000,33871860516⟩
theorem rev153_plane17_mem : rev153_plane17 ∈ rev153_planes := by decide
def rev153_plane37 : IntegerPlane := ⟨2099728000000,1393416000000,2133599860516⟩
theorem rev153_plane37_mem : rev153_plane37 ∈ rev153_planes := by decide
def rev153_plane53 : IntegerPlane := ⟨1468788000000,(-2093220000000),(-880675273104)⟩
theorem rev153_plane53_mem : rev153_plane53 ∈ rev153_planes := by decide
def rev153_plane70 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-2349463273104)⟩
theorem rev153_plane70_mem : rev153_plane70 ∈ rev153_planes := by decide
def rev153_vertex0 : FractionPoint := fractionRow153[0]!
theorem rev153_vertex0_mem : rev153_vertex0∈fractionRow153 := by decide
def rev153_vertex1 : FractionPoint := fractionRow153[1]!
theorem rev153_vertex1_mem : rev153_vertex1∈fractionRow153 := by decide
def rev153_vertex2 : FractionPoint := fractionRow153[2]!
theorem rev153_vertex2_mem : rev153_vertex2∈fractionRow153 := by decide
def rev153_vertex3 : FractionPoint := fractionRow153[3]!
theorem rev153_vertex3_mem : rev153_vertex3∈fractionRow153 := by decide
def rev153_s0_ll : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev153_s0_ll_mem : rev153_s0_ll.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane70 rev153_vertex1 rev153_vertex2 rev153_s0_ll
    rev153_vertex1_mem rev153_vertex2_mem (by decide)
def rev153_s0_lr : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev153_s0_lr_mem : rev153_s0_lr.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane70 rev153_vertex1 rev153_vertex2 rev153_s0_lr
    rev153_vertex1_mem rev153_vertex2_mem (by decide)
def rev153_s0_ul : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev153_s0_ul_mem : rev153_s0_ul.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane17 rev153_vertex1 rev153_vertex0 rev153_s0_ul
    rev153_vertex1_mem rev153_vertex0_mem (by decide)
def rev153_s0_ur : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev153_s0_ur_mem : rev153_s0_ur.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane17 rev153_vertex1 rev153_vertex0 rev153_s0_ur
    rev153_vertex1_mem rev153_vertex0_mem (by decide)
theorem rev153_slab0 (p : Point) (hp : p∈IntegerCarrier rev153_planes)
    (hx0 : rev153_s0_ll.real.1≤p.1) (hx1 : p.1≤rev153_s0_lr.real.1) :
    p∈rationalHull (fractionRow153.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev153_plane70 rev153_plane17 rev153_s0_ll rev153_s0_lr rev153_s0_ul rev153_s0_ur
    (by decide) rev153_s0_ll_mem rev153_s0_lr_mem rev153_s0_ul_mem rev153_s0_ur_mem p
    (hp _ rev153_plane70_mem) (hp _ rev153_plane17_mem) hx0 hx1
def rev153_s1_ll : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev153_s1_ll_mem : rev153_s1_ll.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane53 rev153_vertex2 rev153_vertex3 rev153_s1_ll
    rev153_vertex2_mem rev153_vertex3_mem (by decide)
def rev153_s1_lr : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev153_s1_lr_mem : rev153_s1_lr.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane53 rev153_vertex2 rev153_vertex3 rev153_s1_lr
    rev153_vertex2_mem rev153_vertex3_mem (by decide)
def rev153_s1_ul : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev153_s1_ul_mem : rev153_s1_ul.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane37 rev153_vertex0 rev153_vertex3 rev153_s1_ul
    rev153_vertex0_mem rev153_vertex3_mem (by decide)
def rev153_s1_ur : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev153_s1_ur_mem : rev153_s1_ur.real ∈ rationalHull (fractionRow153.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow153 rev153_plane37 rev153_vertex0 rev153_vertex3 rev153_s1_ur
    rev153_vertex0_mem rev153_vertex3_mem (by decide)
theorem rev153_slab1 (p : Point) (hp : p∈IntegerCarrier rev153_planes)
    (hx0 : rev153_s1_ll.real.1≤p.1) (hx1 : p.1≤rev153_s1_lr.real.1) :
    p∈rationalHull (fractionRow153.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev153_plane53 rev153_plane37 rev153_s1_ll rev153_s1_lr rev153_s1_ul rev153_s1_ur
    (by decide) rev153_s1_ll_mem rev153_s1_lr_mem rev153_s1_ul_mem rev153_s1_ur_mem p
    (hp _ rev153_plane53_mem) (hp _ rev153_plane37_mem) hx0 hx1
theorem rev153_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev153_planes) : rev153_s0_ll.real.1≤p.1 := by
  have hc := rev153_plane17.combine_sound rev153_plane70 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev153_plane17_mem) (hp _ rev153_plane70_mem)
  exact (rev153_plane17.combine rev153_plane70 2093220000000 1393416000000).xBoundCheck_sound rev153_s0_ll.nx rev153_s0_ll.dx true (by decide) p hc
theorem rev153_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev153_planes) : p.1≤rev153_s1_lr.real.1 := by
  have hc := rev153_plane37.combine_sound rev153_plane53 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev153_plane37_mem) (hp _ rev153_plane53_mem)
  exact (rev153_plane37.combine rev153_plane53 2093220000000 1393416000000).xBoundCheck_sound rev153_s1_lr.nx rev153_s1_lr.dx false (by decide) p hc
theorem rev153_hull (p : Point) (hp : p∈IntegerCarrier rev153_planes) :
    p∈rationalHull (fractionRow153.map FractionPoint.rational) := by
  have hxlo := rev153_bound0_lo p hp
  have hxhi := rev153_bound0_hi p hp
  by_cases h0 : p.1≤rev153_s0_lr.real.1
  · exact rev153_slab0 p hp hxlo h0
  exact rev153_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull153 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,10,4,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow153 := by
  rw [← fractionRow153_correct]
  exact rev153_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull153
