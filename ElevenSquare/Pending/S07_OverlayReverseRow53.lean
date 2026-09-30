import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev53_planes : List IntegerPlane := integerOverlayPlanes ![4,11,5,5]
def rev53_plane13 : IntegerPlane := ⟨2093220000000,1468788000000,1212544726896⟩
theorem rev53_plane13_mem : rev53_plane13 ∈ rev53_planes := by decide
def rev53_plane30 : IntegerPlane := ⟨2093220000000,(-1468788000000),(-256243273104)⟩
theorem rev53_plane30_mem : rev53_plane30 ∈ rev53_planes := by decide
def rev53_plane46 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-1359544139484)⟩
theorem rev53_plane46_mem : rev53_plane46 ∈ rev53_planes := by decide
def rev53_plane66 : IntegerPlane := ⟨(-1393416000000),2099728000000,740183860516⟩
theorem rev53_plane66_mem : rev53_plane66 ∈ rev53_planes := by decide
def rev53_vertex0 : FractionPoint := fractionRow53[0]!
theorem rev53_vertex0_mem : rev53_vertex0∈fractionRow53 := by decide
def rev53_vertex1 : FractionPoint := fractionRow53[1]!
theorem rev53_vertex1_mem : rev53_vertex1∈fractionRow53 := by decide
def rev53_vertex2 : FractionPoint := fractionRow53[2]!
theorem rev53_vertex2_mem : rev53_vertex2∈fractionRow53 := by decide
def rev53_vertex3 : FractionPoint := fractionRow53[3]!
theorem rev53_vertex3_mem : rev53_vertex3∈fractionRow53 := by decide
def rev53_s0_ll : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev53_s0_ll_mem : rev53_s0_ll.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane46 rev53_vertex3 rev53_vertex0 rev53_s0_ll
    rev53_vertex3_mem rev53_vertex0_mem (by decide)
def rev53_s0_lr : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev53_s0_lr_mem : rev53_s0_lr.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane46 rev53_vertex3 rev53_vertex0 rev53_s0_lr
    rev53_vertex3_mem rev53_vertex0_mem (by decide)
def rev53_s0_ul : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev53_s0_ul_mem : rev53_s0_ul.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane66 rev53_vertex3 rev53_vertex2 rev53_s0_ul
    rev53_vertex3_mem rev53_vertex2_mem (by decide)
def rev53_s0_ur : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev53_s0_ur_mem : rev53_s0_ur.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane66 rev53_vertex3 rev53_vertex2 rev53_s0_ur
    rev53_vertex3_mem rev53_vertex2_mem (by decide)
theorem rev53_slab0 (p : Point) (hp : p∈IntegerCarrier rev53_planes)
    (hx0 : rev53_s0_ll.real.1≤p.1) (hx1 : p.1≤rev53_s0_lr.real.1) :
    p∈rationalHull (fractionRow53.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev53_plane46 rev53_plane66 rev53_s0_ll rev53_s0_lr rev53_s0_ul rev53_s0_ur
    (by decide) rev53_s0_ll_mem rev53_s0_lr_mem rev53_s0_ul_mem rev53_s0_ur_mem p
    (hp _ rev53_plane46_mem) (hp _ rev53_plane66_mem) hx0 hx1
def rev53_s1_ll : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev53_s1_ll_mem : rev53_s1_ll.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane30 rev53_vertex0 rev53_vertex1 rev53_s1_ll
    rev53_vertex0_mem rev53_vertex1_mem (by decide)
def rev53_s1_lr : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev53_s1_lr_mem : rev53_s1_lr.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane30 rev53_vertex0 rev53_vertex1 rev53_s1_lr
    rev53_vertex0_mem rev53_vertex1_mem (by decide)
def rev53_s1_ul : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev53_s1_ul_mem : rev53_s1_ul.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane13 rev53_vertex2 rev53_vertex1 rev53_s1_ul
    rev53_vertex2_mem rev53_vertex1_mem (by decide)
def rev53_s1_ur : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev53_s1_ur_mem : rev53_s1_ur.real ∈ rationalHull (fractionRow53.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow53 rev53_plane13 rev53_vertex2 rev53_vertex1 rev53_s1_ur
    rev53_vertex2_mem rev53_vertex1_mem (by decide)
theorem rev53_slab1 (p : Point) (hp : p∈IntegerCarrier rev53_planes)
    (hx0 : rev53_s1_ll.real.1≤p.1) (hx1 : p.1≤rev53_s1_lr.real.1) :
    p∈rationalHull (fractionRow53.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev53_plane30 rev53_plane13 rev53_s1_ll rev53_s1_lr rev53_s1_ul rev53_s1_ur
    (by decide) rev53_s1_ll_mem rev53_s1_lr_mem rev53_s1_ul_mem rev53_s1_ur_mem p
    (hp _ rev53_plane30_mem) (hp _ rev53_plane13_mem) hx0 hx1
theorem rev53_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev53_planes) : rev53_s0_ll.real.1≤p.1 := by
  have hc := rev53_plane46.combine_sound rev53_plane66 2099728000000 2099728000000 (by decide) (by decide) p
    (hp _ rev53_plane46_mem) (hp _ rev53_plane66_mem)
  exact (rev53_plane46.combine rev53_plane66 2099728000000 2099728000000).xBoundCheck_sound rev53_s0_ll.nx rev53_s0_ll.dx true (by decide) p hc
theorem rev53_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev53_planes) : p.1≤rev53_s1_lr.real.1 := by
  have hc := rev53_plane13.combine_sound rev53_plane30 1468788000000 1468788000000 (by decide) (by decide) p
    (hp _ rev53_plane13_mem) (hp _ rev53_plane30_mem)
  exact (rev53_plane13.combine rev53_plane30 1468788000000 1468788000000).xBoundCheck_sound rev53_s1_lr.nx rev53_s1_lr.dx false (by decide) p hc
theorem rev53_hull (p : Point) (hp : p∈IntegerCarrier rev53_planes) :
    p∈rationalHull (fractionRow53.map FractionPoint.rational) := by
  have hxlo := rev53_bound0_lo p hp
  have hxhi := rev53_bound0_hi p hp
  by_cases h0 : p.1≤rev53_s0_lr.real.1
  · exact rev53_slab0 p hp hxlo h0
  exact rev53_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull53 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,11,5,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow53 := by
  rw [← fractionRow53_correct]
  exact rev53_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull53
