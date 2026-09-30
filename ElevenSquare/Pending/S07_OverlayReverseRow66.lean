import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev66_planes : List IntegerPlane := integerOverlayPlanes ![5,5,11,4]
def rev66_plane6 : IntegerPlane := ⟨2099728000000,(-1393416000000),740183860516⟩
theorem rev66_plane6_mem : rev66_plane6 ∈ rev66_planes := by decide
def rev66_plane26 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-1359544139484)⟩
theorem rev66_plane26_mem : rev66_plane26 ∈ rev66_planes := by decide
def rev66_plane50 : IntegerPlane := ⟨(-1468788000000),2093220000000,(-256243273104)⟩
theorem rev66_plane50_mem : rev66_plane50 ∈ rev66_planes := by decide
def rev66_plane73 : IntegerPlane := ⟨1468788000000,2093220000000,1212544726896⟩
theorem rev66_plane73_mem : rev66_plane73 ∈ rev66_planes := by decide
def rev66_vertex0 : FractionPoint := fractionRow66[0]!
theorem rev66_vertex0_mem : rev66_vertex0∈fractionRow66 := by decide
def rev66_vertex1 : FractionPoint := fractionRow66[1]!
theorem rev66_vertex1_mem : rev66_vertex1∈fractionRow66 := by decide
def rev66_vertex2 : FractionPoint := fractionRow66[2]!
theorem rev66_vertex2_mem : rev66_vertex2∈fractionRow66 := by decide
def rev66_vertex3 : FractionPoint := fractionRow66[3]!
theorem rev66_vertex3_mem : rev66_vertex3∈fractionRow66 := by decide
def rev66_s0_ll : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev66_s0_ll_mem : rev66_s0_ll.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane26 rev66_vertex3 rev66_vertex0 rev66_s0_ll
    rev66_vertex3_mem rev66_vertex0_mem (by decide)
def rev66_s0_lr : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev66_s0_lr_mem : rev66_s0_lr.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane26 rev66_vertex3 rev66_vertex0 rev66_s0_lr
    rev66_vertex3_mem rev66_vertex0_mem (by decide)
def rev66_s0_ul : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev66_s0_ul_mem : rev66_s0_ul.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane50 rev66_vertex3 rev66_vertex2 rev66_s0_ul
    rev66_vertex3_mem rev66_vertex2_mem (by decide)
def rev66_s0_ur : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev66_s0_ur_mem : rev66_s0_ur.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane50 rev66_vertex3 rev66_vertex2 rev66_s0_ur
    rev66_vertex3_mem rev66_vertex2_mem (by decide)
theorem rev66_slab0 (p : Point) (hp : p∈IntegerCarrier rev66_planes)
    (hx0 : rev66_s0_ll.real.1≤p.1) (hx1 : p.1≤rev66_s0_lr.real.1) :
    p∈rationalHull (fractionRow66.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev66_plane26 rev66_plane50 rev66_s0_ll rev66_s0_lr rev66_s0_ul rev66_s0_ur
    (by decide) rev66_s0_ll_mem rev66_s0_lr_mem rev66_s0_ul_mem rev66_s0_ur_mem p
    (hp _ rev66_plane26_mem) (hp _ rev66_plane50_mem) hx0 hx1
def rev66_s1_ll : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev66_s1_ll_mem : rev66_s1_ll.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane6 rev66_vertex0 rev66_vertex1 rev66_s1_ll
    rev66_vertex0_mem rev66_vertex1_mem (by decide)
def rev66_s1_lr : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev66_s1_lr_mem : rev66_s1_lr.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane6 rev66_vertex0 rev66_vertex1 rev66_s1_lr
    rev66_vertex0_mem rev66_vertex1_mem (by decide)
def rev66_s1_ul : FractionPoint := ⟨1,2,3320491159,14536250000⟩
theorem rev66_s1_ul_mem : rev66_s1_ul.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane73 rev66_vertex2 rev66_vertex1 rev66_s1_ul
    rev66_vertex2_mem rev66_vertex1_mem (by decide)
def rev66_s1_ur : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev66_s1_ur_mem : rev66_s1_ur.real ∈ rationalHull (fractionRow66.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow66 rev66_plane73 rev66_vertex2 rev66_vertex1 rev66_s1_ur
    rev66_vertex2_mem rev66_vertex1_mem (by decide)
theorem rev66_slab1 (p : Point) (hp : p∈IntegerCarrier rev66_planes)
    (hx0 : rev66_s1_ll.real.1≤p.1) (hx1 : p.1≤rev66_s1_lr.real.1) :
    p∈rationalHull (fractionRow66.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev66_plane6 rev66_plane73 rev66_s1_ll rev66_s1_lr rev66_s1_ul rev66_s1_ur
    (by decide) rev66_s1_ll_mem rev66_s1_lr_mem rev66_s1_ul_mem rev66_s1_ur_mem p
    (hp _ rev66_plane6_mem) (hp _ rev66_plane73_mem) hx0 hx1
theorem rev66_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev66_planes) : rev66_s0_ll.real.1≤p.1 := by
  have hc := rev66_plane26.combine_sound rev66_plane50 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev66_plane26_mem) (hp _ rev66_plane50_mem)
  exact (rev66_plane26.combine rev66_plane50 2093220000000 1393416000000).xBoundCheck_sound rev66_s0_ll.nx rev66_s0_ll.dx true (by decide) p hc
theorem rev66_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev66_planes) : p.1≤rev66_s1_lr.real.1 := by
  have hc := rev66_plane6.combine_sound rev66_plane73 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev66_plane6_mem) (hp _ rev66_plane73_mem)
  exact (rev66_plane6.combine rev66_plane73 2093220000000 1393416000000).xBoundCheck_sound rev66_s1_lr.nx rev66_s1_lr.dx false (by decide) p hc
theorem rev66_hull (p : Point) (hp : p∈IntegerCarrier rev66_planes) :
    p∈rationalHull (fractionRow66.map FractionPoint.rational) := by
  have hxlo := rev66_bound0_lo p hp
  have hxhi := rev66_bound0_hi p hp
  by_cases h0 : p.1≤rev66_s0_lr.real.1
  · exact rev66_slab0 p hp hxlo h0
  exact rev66_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull66 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,5,11,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow66 := by
  rw [← fractionRow66_correct]
  exact rev66_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull66
