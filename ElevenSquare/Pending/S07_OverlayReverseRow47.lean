import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev47_planes : List IntegerPlane := integerOverlayPlanes ![4,11,1,1]
def rev47_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev47_plane0_mem : rev47_plane0 ∈ rev47_planes := by decide
def rev47_plane12 : IntegerPlane := ⟨48252000000,2112760000000,1130009250915⟩
theorem rev47_plane12_mem : rev47_plane12 ∈ rev47_planes := by decide
def rev47_plane31 : IntegerPlane := ⟨48252000000,(-2112760000000),(-982750749085)⟩
theorem rev47_plane31_mem : rev47_plane31 ∈ rev47_planes := by decide
def rev47_plane46 : IntegerPlane := ⟨746024000000,(-2083356000000),(-965839292059)⟩
theorem rev47_plane46_mem : rev47_plane46 ∈ rev47_planes := by decide
def rev47_plane66 : IntegerPlane := ⟨746024000000,2083356000000,1117516707941⟩
theorem rev47_plane66_mem : rev47_plane66 ∈ rev47_planes := by decide
def rev47_vertex0 : FractionPoint := fractionRow47[0]!
theorem rev47_vertex0_mem : rev47_vertex0∈fractionRow47 := by decide
def rev47_vertex1 : FractionPoint := fractionRow47[1]!
theorem rev47_vertex1_mem : rev47_vertex1∈fractionRow47 := by decide
def rev47_vertex2 : FractionPoint := fractionRow47[2]!
theorem rev47_vertex2_mem : rev47_vertex2∈fractionRow47 := by decide
def rev47_vertex3 : FractionPoint := fractionRow47[3]!
theorem rev47_vertex3_mem : rev47_vertex3∈fractionRow47 := by decide
def rev47_vertex4 : FractionPoint := fractionRow47[4]!
theorem rev47_vertex4_mem : rev47_vertex4∈fractionRow47 := by decide
def rev47_s0_ll : FractionPoint := ⟨0,1,196550149817,422552000000⟩
theorem rev47_s0_ll_mem : rev47_s0_ll.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane31 rev47_vertex1 rev47_vertex2 rev47_s0_ll
    rev47_vertex1_mem rev47_vertex2_mem (by decide)
def rev47_s0_lr : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev47_s0_lr_mem : rev47_s0_lr.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane31 rev47_vertex1 rev47_vertex2 rev47_s0_lr
    rev47_vertex1_mem rev47_vertex2_mem (by decide)
def rev47_s0_ul : FractionPoint := ⟨0,1,226001850183,422552000000⟩
theorem rev47_s0_ul_mem : rev47_s0_ul.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane12 rev47_vertex0 rev47_vertex4 rev47_s0_ul
    rev47_vertex0_mem rev47_vertex4_mem (by decide)
def rev47_s0_ur : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev47_s0_ur_mem : rev47_s0_ur.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane12 rev47_vertex0 rev47_vertex4 rev47_s0_ur
    rev47_vertex0_mem rev47_vertex4_mem (by decide)
theorem rev47_slab0 (p : Point) (hp : p∈IntegerCarrier rev47_planes)
    (hx0 : rev47_s0_ll.real.1≤p.1) (hx1 : p.1≤rev47_s0_lr.real.1) :
    p∈rationalHull (fractionRow47.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev47_plane31 rev47_plane12 rev47_s0_ll rev47_s0_lr rev47_s0_ul rev47_s0_ur
    (by decide) rev47_s0_ll_mem rev47_s0_lr_mem rev47_s0_ul_mem rev47_s0_ur_mem p
    (hp _ rev47_plane31_mem) (hp _ rev47_plane12_mem) hx0 hx1
def rev47_s1_ll : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev47_s1_ll_mem : rev47_s1_ll.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane46 rev47_vertex2 rev47_vertex3 rev47_s1_ll
    rev47_vertex2_mem rev47_vertex3_mem (by decide)
def rev47_s1_lr : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev47_s1_lr_mem : rev47_s1_lr.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane46 rev47_vertex2 rev47_vertex3 rev47_s1_lr
    rev47_vertex2_mem rev47_vertex3_mem (by decide)
def rev47_s1_ul : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev47_s1_ul_mem : rev47_s1_ul.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane66 rev47_vertex4 rev47_vertex3 rev47_s1_ul
    rev47_vertex4_mem rev47_vertex3_mem (by decide)
def rev47_s1_ur : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev47_s1_ur_mem : rev47_s1_ur.real ∈ rationalHull (fractionRow47.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow47 rev47_plane66 rev47_vertex4 rev47_vertex3 rev47_s1_ur
    rev47_vertex4_mem rev47_vertex3_mem (by decide)
theorem rev47_slab1 (p : Point) (hp : p∈IntegerCarrier rev47_planes)
    (hx0 : rev47_s1_ll.real.1≤p.1) (hx1 : p.1≤rev47_s1_lr.real.1) :
    p∈rationalHull (fractionRow47.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev47_plane46 rev47_plane66 rev47_s1_ll rev47_s1_lr rev47_s1_ul rev47_s1_ur
    (by decide) rev47_s1_ll_mem rev47_s1_lr_mem rev47_s1_ul_mem rev47_s1_ur_mem p
    (hp _ rev47_plane46_mem) (hp _ rev47_plane66_mem) hx0 hx1
theorem rev47_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev47_planes) : rev47_s0_ll.real.1≤p.1 := by
  have hc := rev47_plane0.combine_sound rev47_plane0 1 0 (by decide) (by decide) p
    (hp _ rev47_plane0_mem) (hp _ rev47_plane0_mem)
  exact (rev47_plane0.combine rev47_plane0 1 0).xBoundCheck_sound rev47_s0_ll.nx rev47_s0_ll.dx true (by decide) p hc
theorem rev47_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev47_planes) : p.1≤rev47_s1_lr.real.1 := by
  have hc := rev47_plane46.combine_sound rev47_plane66 2083356000000 2083356000000 (by decide) (by decide) p
    (hp _ rev47_plane46_mem) (hp _ rev47_plane66_mem)
  exact (rev47_plane46.combine rev47_plane66 2083356000000 2083356000000).xBoundCheck_sound rev47_s1_lr.nx rev47_s1_lr.dx false (by decide) p hc
theorem rev47_hull (p : Point) (hp : p∈IntegerCarrier rev47_planes) :
    p∈rationalHull (fractionRow47.map FractionPoint.rational) := by
  have hxlo := rev47_bound0_lo p hp
  have hxhi := rev47_bound0_hi p hp
  by_cases h0 : p.1≤rev47_s0_lr.real.1
  · exact rev47_slab0 p hp hxlo h0
  exact rev47_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull47 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,11,1,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow47 := by
  rw [← fractionRow47_correct]
  exact rev47_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull47
