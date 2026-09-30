import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev155_planes : List IntegerPlane := integerOverlayPlanes ![10,10,9,11]
def rev155_plane37 : IntegerPlane := ⟨2099728000000,1393416000000,2133599860516⟩
theorem rev155_plane37_mem : rev155_plane37 ∈ rev155_planes := by decide
def rev155_plane48 : IntegerPlane := ⟨(-1468788000000),2093220000000,880675273104⟩
theorem rev155_plane48_mem : rev155_plane48 ∈ rev155_planes := by decide
def rev155_plane70 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-2349463273104)⟩
theorem rev155_plane70_mem : rev155_plane70 ∈ rev155_planes := by decide
def rev155_vertex0 : FractionPoint := fractionRow155[0]!
theorem rev155_vertex0_mem : rev155_vertex0∈fractionRow155 := by decide
def rev155_vertex1 : FractionPoint := fractionRow155[1]!
theorem rev155_vertex1_mem : rev155_vertex1∈fractionRow155 := by decide
def rev155_vertex2 : FractionPoint := fractionRow155[2]!
theorem rev155_vertex2_mem : rev155_vertex2∈fractionRow155 := by decide
def rev155_s0_ll : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev155_s0_ll_mem : rev155_s0_ll.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane70 rev155_vertex2 rev155_vertex0 rev155_s0_ll
    rev155_vertex2_mem rev155_vertex0_mem (by decide)
def rev155_s0_lr : FractionPoint := ⟨22492686692234849,44734898222000000,6005501008110015885673,7803331971354570000000⟩
theorem rev155_s0_lr_mem : rev155_s0_lr.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane70 rev155_vertex2 rev155_vertex0 rev155_s0_lr
    rev155_vertex2_mem rev155_vertex0_mem (by decide)
def rev155_s0_ul : FractionPoint := ⟨1,2,11215758841,14536250000⟩
theorem rev155_s0_ul_mem : rev155_s0_ul.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane48 rev155_vertex2 rev155_vertex1 rev155_s0_ul
    rev155_vertex2_mem rev155_vertex1_mem (by decide)
def rev155_s0_ur : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev155_s0_ur_mem : rev155_s0_ur.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane48 rev155_vertex2 rev155_vertex1 rev155_s0_ur
    rev155_vertex2_mem rev155_vertex1_mem (by decide)
theorem rev155_slab0 (p : Point) (hp : p∈IntegerCarrier rev155_planes)
    (hx0 : rev155_s0_ll.real.1≤p.1) (hx1 : p.1≤rev155_s0_lr.real.1) :
    p∈rationalHull (fractionRow155.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev155_plane70 rev155_plane48 rev155_s0_ll rev155_s0_lr rev155_s0_ul rev155_s0_ur
    (by decide) rev155_s0_ll_mem rev155_s0_lr_mem rev155_s0_ul_mem rev155_s0_ur_mem p
    (hp _ rev155_plane70_mem) (hp _ rev155_plane48_mem) hx0 hx1
def rev155_s1_ll : FractionPoint := ⟨22492686692234849,44734898222000000,6005501008110015885673,7803331971354570000000⟩
theorem rev155_s1_ll_mem : rev155_s1_ll.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane70 rev155_vertex2 rev155_vertex0 rev155_s1_ll
    rev155_vertex2_mem rev155_vertex0_mem (by decide)
def rev155_s1_lr : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev155_s1_lr_mem : rev155_s1_lr.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane70 rev155_vertex2 rev155_vertex0 rev155_s1_lr
    rev155_vertex2_mem rev155_vertex0_mem (by decide)
def rev155_s1_ul : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev155_s1_ul_mem : rev155_s1_ul.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane37 rev155_vertex1 rev155_vertex0 rev155_s1_ul
    rev155_vertex1_mem rev155_vertex0_mem (by decide)
def rev155_s1_ur : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev155_s1_ur_mem : rev155_s1_ur.real ∈ rationalHull (fractionRow155.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow155 rev155_plane37 rev155_vertex1 rev155_vertex0 rev155_s1_ur
    rev155_vertex1_mem rev155_vertex0_mem (by decide)
theorem rev155_slab1 (p : Point) (hp : p∈IntegerCarrier rev155_planes)
    (hx0 : rev155_s1_ll.real.1≤p.1) (hx1 : p.1≤rev155_s1_lr.real.1) :
    p∈rationalHull (fractionRow155.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev155_plane70 rev155_plane37 rev155_s1_ll rev155_s1_lr rev155_s1_ul rev155_s1_ur
    (by decide) rev155_s1_ll_mem rev155_s1_lr_mem rev155_s1_ul_mem rev155_s1_ur_mem p
    (hp _ rev155_plane70_mem) (hp _ rev155_plane37_mem) hx0 hx1
theorem rev155_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev155_planes) : rev155_s0_ll.real.1≤p.1 := by
  have hc := rev155_plane48.combine_sound rev155_plane70 2093220000000 2093220000000 (by decide) (by decide) p
    (hp _ rev155_plane48_mem) (hp _ rev155_plane70_mem)
  exact (rev155_plane48.combine rev155_plane70 2093220000000 2093220000000).xBoundCheck_sound rev155_s0_ll.nx rev155_s0_ll.dx true (by decide) p hc
theorem rev155_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev155_planes) : p.1≤rev155_s1_lr.real.1 := by
  have hc := rev155_plane37.combine_sound rev155_plane70 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev155_plane37_mem) (hp _ rev155_plane70_mem)
  exact (rev155_plane37.combine rev155_plane70 2093220000000 1393416000000).xBoundCheck_sound rev155_s1_lr.nx rev155_s1_lr.dx false (by decide) p hc
theorem rev155_hull (p : Point) (hp : p∈IntegerCarrier rev155_planes) :
    p∈rationalHull (fractionRow155.map FractionPoint.rational) := by
  have hxlo := rev155_bound0_lo p hp
  have hxhi := rev155_bound0_hi p hp
  by_cases h0 : p.1≤rev155_s0_lr.real.1
  · exact rev155_slab0 p hp hxlo h0
  exact rev155_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull155 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,10,9,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow155 := by
  rw [← fractionRow155_correct]
  exact rev155_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull155
