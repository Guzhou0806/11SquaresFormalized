import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev166_planes : List IntegerPlane := integerOverlayPlanes ![11,4,10,10]
def rev166_plane10 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-2349463273104)⟩
theorem rev166_plane10_mem : rev166_plane10 ∈ rev166_planes := by decide
def rev166_plane33 : IntegerPlane := ⟨(-2093220000000),1468788000000,(-880675273104)⟩
theorem rev166_plane33_mem : rev166_plane33 ∈ rev166_planes := by decide
def rev166_plane57 : IntegerPlane := ⟨1393416000000,2099728000000,2133599860516⟩
theorem rev166_plane57_mem : rev166_plane57 ∈ rev166_planes := by decide
def rev166_plane77 : IntegerPlane := ⟨1393416000000,(-2099728000000),33871860516⟩
theorem rev166_plane77_mem : rev166_plane77 ∈ rev166_planes := by decide
def rev166_vertex0 : FractionPoint := fractionRow166[0]!
theorem rev166_vertex0_mem : rev166_vertex0∈fractionRow166 := by decide
def rev166_vertex1 : FractionPoint := fractionRow166[1]!
theorem rev166_vertex1_mem : rev166_vertex1∈fractionRow166 := by decide
def rev166_vertex2 : FractionPoint := fractionRow166[2]!
theorem rev166_vertex2_mem : rev166_vertex2∈fractionRow166 := by decide
def rev166_vertex3 : FractionPoint := fractionRow166[3]!
theorem rev166_vertex3_mem : rev166_vertex3∈fractionRow166 := by decide
def rev166_s0_ll : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev166_s0_ll_mem : rev166_s0_ll.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane10 rev166_vertex1 rev166_vertex2 rev166_s0_ll
    rev166_vertex1_mem rev166_vertex2_mem (by decide)
def rev166_s0_lr : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev166_s0_lr_mem : rev166_s0_lr.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane10 rev166_vertex1 rev166_vertex2 rev166_s0_lr
    rev166_vertex1_mem rev166_vertex2_mem (by decide)
def rev166_s0_ul : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev166_s0_ul_mem : rev166_s0_ul.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane33 rev166_vertex1 rev166_vertex0 rev166_s0_ul
    rev166_vertex1_mem rev166_vertex0_mem (by decide)
def rev166_s0_ur : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev166_s0_ur_mem : rev166_s0_ur.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane33 rev166_vertex1 rev166_vertex0 rev166_s0_ur
    rev166_vertex1_mem rev166_vertex0_mem (by decide)
theorem rev166_slab0 (p : Point) (hp : p∈IntegerCarrier rev166_planes)
    (hx0 : rev166_s0_ll.real.1≤p.1) (hx1 : p.1≤rev166_s0_lr.real.1) :
    p∈rationalHull (fractionRow166.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev166_plane10 rev166_plane33 rev166_s0_ll rev166_s0_lr rev166_s0_ul rev166_s0_ur
    (by decide) rev166_s0_ll_mem rev166_s0_lr_mem rev166_s0_ul_mem rev166_s0_ur_mem p
    (hp _ rev166_plane10_mem) (hp _ rev166_plane33_mem) hx0 hx1
def rev166_s1_ll : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev166_s1_ll_mem : rev166_s1_ll.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane77 rev166_vertex2 rev166_vertex3 rev166_s1_ll
    rev166_vertex2_mem rev166_vertex3_mem (by decide)
def rev166_s1_lr : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev166_s1_lr_mem : rev166_s1_lr.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane77 rev166_vertex2 rev166_vertex3 rev166_s1_lr
    rev166_vertex2_mem rev166_vertex3_mem (by decide)
def rev166_s1_ul : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev166_s1_ul_mem : rev166_s1_ul.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane57 rev166_vertex0 rev166_vertex3 rev166_s1_ul
    rev166_vertex0_mem rev166_vertex3_mem (by decide)
def rev166_s1_ur : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev166_s1_ur_mem : rev166_s1_ur.real ∈ rationalHull (fractionRow166.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow166 rev166_plane57 rev166_vertex0 rev166_vertex3 rev166_s1_ur
    rev166_vertex0_mem rev166_vertex3_mem (by decide)
theorem rev166_slab1 (p : Point) (hp : p∈IntegerCarrier rev166_planes)
    (hx0 : rev166_s1_ll.real.1≤p.1) (hx1 : p.1≤rev166_s1_lr.real.1) :
    p∈rationalHull (fractionRow166.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev166_plane77 rev166_plane57 rev166_s1_ll rev166_s1_lr rev166_s1_ul rev166_s1_ur
    (by decide) rev166_s1_ll_mem rev166_s1_lr_mem rev166_s1_ul_mem rev166_s1_ur_mem p
    (hp _ rev166_plane77_mem) (hp _ rev166_plane57_mem) hx0 hx1
theorem rev166_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev166_planes) : rev166_s0_ll.real.1≤p.1 := by
  have hc := rev166_plane10.combine_sound rev166_plane33 1468788000000 1468788000000 (by decide) (by decide) p
    (hp _ rev166_plane10_mem) (hp _ rev166_plane33_mem)
  exact (rev166_plane10.combine rev166_plane33 1468788000000 1468788000000).xBoundCheck_sound rev166_s0_ll.nx rev166_s0_ll.dx true (by decide) p hc
theorem rev166_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev166_planes) : p.1≤rev166_s1_lr.real.1 := by
  have hc := rev166_plane57.combine_sound rev166_plane77 2099728000000 2099728000000 (by decide) (by decide) p
    (hp _ rev166_plane57_mem) (hp _ rev166_plane77_mem)
  exact (rev166_plane57.combine rev166_plane77 2099728000000 2099728000000).xBoundCheck_sound rev166_s1_lr.nx rev166_s1_lr.dx false (by decide) p hc
theorem rev166_hull (p : Point) (hp : p∈IntegerCarrier rev166_planes) :
    p∈rationalHull (fractionRow166.map FractionPoint.rational) := by
  have hxlo := rev166_bound0_lo p hp
  have hxhi := rev166_bound0_hi p hp
  by_cases h0 : p.1≤rev166_s0_lr.real.1
  · exact rev166_slab0 p hp hxlo h0
  exact rev166_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull166 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,4,10,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow166 := by
  rw [← fractionRow166_correct]
  exact rev166_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull166
