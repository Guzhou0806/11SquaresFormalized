import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks22
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev178_planes : List IntegerPlane := integerOverlayPlanes ![11,9,10,10]
def rev178_plane10 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-2349463273104)⟩
theorem rev178_plane10_mem : rev178_plane10 ∈ rev178_planes := by decide
def rev178_plane28 : IntegerPlane := ⟨2093220000000,(-1468788000000),880675273104⟩
theorem rev178_plane28_mem : rev178_plane28 ∈ rev178_planes := by decide
def rev178_plane57 : IntegerPlane := ⟨1393416000000,2099728000000,2133599860516⟩
theorem rev178_plane57_mem : rev178_plane57 ∈ rev178_planes := by decide
def rev178_vertex0 : FractionPoint := fractionRow178[0]!
theorem rev178_vertex0_mem : rev178_vertex0∈fractionRow178 := by decide
def rev178_vertex1 : FractionPoint := fractionRow178[1]!
theorem rev178_vertex1_mem : rev178_vertex1∈fractionRow178 := by decide
def rev178_vertex2 : FractionPoint := fractionRow178[2]!
theorem rev178_vertex2_mem : rev178_vertex2∈fractionRow178 := by decide
def rev178_s0_ll : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev178_s0_ll_mem : rev178_s0_ll.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane10 rev178_vertex0 rev178_vertex1 rev178_s0_ll
    rev178_vertex0_mem rev178_vertex1_mem (by decide)
def rev178_s0_lr : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev178_s0_lr_mem : rev178_s0_lr.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane10 rev178_vertex0 rev178_vertex1 rev178_s0_lr
    rev178_vertex0_mem rev178_vertex1_mem (by decide)
def rev178_s0_ul : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev178_s0_ul_mem : rev178_s0_ul.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane57 rev178_vertex0 rev178_vertex2 rev178_s0_ul
    rev178_vertex0_mem rev178_vertex2_mem (by decide)
def rev178_s0_ur : FractionPoint := ⟨11215758841,14536250000,15386323151234849,30522171140000000⟩
theorem rev178_s0_ur_mem : rev178_s0_ur.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane57 rev178_vertex0 rev178_vertex2 rev178_s0_ur
    rev178_vertex0_mem rev178_vertex2_mem (by decide)
theorem rev178_slab0 (p : Point) (hp : p∈IntegerCarrier rev178_planes)
    (hx0 : rev178_s0_ll.real.1≤p.1) (hx1 : p.1≤rev178_s0_lr.real.1) :
    p∈rationalHull (fractionRow178.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev178_plane10 rev178_plane57 rev178_s0_ll rev178_s0_lr rev178_s0_ul rev178_s0_ur
    (by decide) rev178_s0_ll_mem rev178_s0_lr_mem rev178_s0_ul_mem rev178_s0_ur_mem p
    (hp _ rev178_plane10_mem) (hp _ rev178_plane57_mem) hx0 hx1
def rev178_s1_ll : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev178_s1_ll_mem : rev178_s1_ll.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane28 rev178_vertex1 rev178_vertex2 rev178_s1_ll
    rev178_vertex1_mem rev178_vertex2_mem (by decide)
def rev178_s1_lr : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev178_s1_lr_mem : rev178_s1_lr.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane28 rev178_vertex1 rev178_vertex2 rev178_s1_lr
    rev178_vertex1_mem rev178_vertex2_mem (by decide)
def rev178_s1_ul : FractionPoint := ⟨11215758841,14536250000,15386323151234849,30522171140000000⟩
theorem rev178_s1_ul_mem : rev178_s1_ul.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane57 rev178_vertex0 rev178_vertex2 rev178_s1_ul
    rev178_vertex0_mem rev178_vertex2_mem (by decide)
def rev178_s1_ur : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev178_s1_ur_mem : rev178_s1_ur.real ∈ rationalHull (fractionRow178.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow178 rev178_plane57 rev178_vertex0 rev178_vertex2 rev178_s1_ur
    rev178_vertex0_mem rev178_vertex2_mem (by decide)
theorem rev178_slab1 (p : Point) (hp : p∈IntegerCarrier rev178_planes)
    (hx0 : rev178_s1_ll.real.1≤p.1) (hx1 : p.1≤rev178_s1_lr.real.1) :
    p∈rationalHull (fractionRow178.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev178_plane28 rev178_plane57 rev178_s1_ll rev178_s1_lr rev178_s1_ul rev178_s1_ur
    (by decide) rev178_s1_ll_mem rev178_s1_lr_mem rev178_s1_ul_mem rev178_s1_ur_mem p
    (hp _ rev178_plane28_mem) (hp _ rev178_plane57_mem) hx0 hx1
theorem rev178_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev178_planes) : rev178_s0_ll.real.1≤p.1 := by
  have hc := rev178_plane10.combine_sound rev178_plane57 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev178_plane10_mem) (hp _ rev178_plane57_mem)
  exact (rev178_plane10.combine rev178_plane57 2099728000000 1468788000000).xBoundCheck_sound rev178_s0_ll.nx rev178_s0_ll.dx true (by decide) p hc
theorem rev178_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev178_planes) : p.1≤rev178_s1_lr.real.1 := by
  have hc := rev178_plane28.combine_sound rev178_plane57 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev178_plane28_mem) (hp _ rev178_plane57_mem)
  exact (rev178_plane28.combine rev178_plane57 2099728000000 1468788000000).xBoundCheck_sound rev178_s1_lr.nx rev178_s1_lr.dx false (by decide) p hc
theorem rev178_hull (p : Point) (hp : p∈IntegerCarrier rev178_planes) :
    p∈rationalHull (fractionRow178.map FractionPoint.rational) := by
  have hxlo := rev178_bound0_lo p hp
  have hxhi := rev178_bound0_hi p hp
  by_cases h0 : p.1≤rev178_s0_lr.real.1
  · exact rev178_slab0 p hp hxlo h0
  exact rev178_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull178 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,9,10,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow178 := by
  rw [← fractionRow178_correct]
  exact rev178_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull178
