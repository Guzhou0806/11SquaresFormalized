import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev49_planes : List IntegerPlane := integerOverlayPlanes ![4,11,2,1]
def rev49_plane31 : IntegerPlane := ⟨48252000000,(-2112760000000),(-982750749085)⟩
theorem rev49_plane31_mem : rev49_plane31 ∈ rev49_planes := by decide
def rev49_plane45 : IntegerPlane := ⟨(-746024000000),2083356000000,965839292059⟩
theorem rev49_plane45_mem : rev49_plane45 ∈ rev49_planes := by decide
def rev49_plane66 : IntegerPlane := ⟨746024000000,2083356000000,1117516707941⟩
theorem rev49_plane66_mem : rev49_plane66 ∈ rev49_planes := by decide
def rev49_plane69 : IntegerPlane := ⟨2139440000000,(-16372000000),377332847425⟩
theorem rev49_plane69_mem : rev49_plane69 ∈ rev49_planes := by decide
def rev49_vertex0 : FractionPoint := fractionRow49[0]!
theorem rev49_vertex0_mem : rev49_vertex0∈fractionRow49 := by decide
def rev49_vertex1 : FractionPoint := fractionRow49[1]!
theorem rev49_vertex1_mem : rev49_vertex1∈fractionRow49 := by decide
def rev49_vertex2 : FractionPoint := fractionRow49[2]!
theorem rev49_vertex2_mem : rev49_vertex2∈fractionRow49 := by decide
def rev49_vertex3 : FractionPoint := fractionRow49[3]!
theorem rev49_vertex3_mem : rev49_vertex3∈fractionRow49 := by decide
def rev49_s0_ll : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev49_s0_ll_mem : rev49_s0_ll.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane31 rev49_vertex0 rev49_vertex1 rev49_s0_ll
    rev49_vertex0_mem rev49_vertex1_mem (by decide)
def rev49_s0_lr : FractionPoint := ⟨75838707941,746024000000,184203753542739293,394042416560000000⟩
theorem rev49_s0_lr_mem : rev49_s0_lr.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane31 rev49_vertex0 rev49_vertex1 rev49_s0_lr
    rev49_vertex0_mem rev49_vertex1_mem (by decide)
def rev49_s0_ul : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev49_s0_ul_mem : rev49_s0_ul.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane45 rev49_vertex0 rev49_vertex3 rev49_s0_ul
    rev49_vertex0_mem rev49_vertex3_mem (by decide)
def rev49_s0_ur : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev49_s0_ur_mem : rev49_s0_ur.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane45 rev49_vertex0 rev49_vertex3 rev49_s0_ur
    rev49_vertex0_mem rev49_vertex3_mem (by decide)
theorem rev49_slab0 (p : Point) (hp : p∈IntegerCarrier rev49_planes)
    (hx0 : rev49_s0_ll.real.1≤p.1) (hx1 : p.1≤rev49_s0_lr.real.1) :
    p∈rationalHull (fractionRow49.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev49_plane31 rev49_plane45 rev49_s0_ll rev49_s0_lr rev49_s0_ul rev49_s0_ur
    (by decide) rev49_s0_ll_mem rev49_s0_lr_mem rev49_s0_ul_mem rev49_s0_ur_mem p
    (hp _ rev49_plane31_mem) (hp _ rev49_plane45_mem) hx0 hx1
def rev49_s1_ll : FractionPoint := ⟨75838707941,746024000000,184203753542739293,394042416560000000⟩
theorem rev49_s1_ll_mem : rev49_s1_ll.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane31 rev49_vertex0 rev49_vertex1 rev49_s1_ll
    rev49_vertex0_mem rev49_vertex1_mem (by decide)
def rev49_s1_lr : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev49_s1_lr_mem : rev49_s1_lr.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane31 rev49_vertex0 rev49_vertex1 rev49_s1_lr
    rev49_vertex0_mem rev49_vertex1_mem (by decide)
def rev49_s1_ul : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev49_s1_ul_mem : rev49_s1_ul.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane66 rev49_vertex3 rev49_vertex2 rev49_s1_ul
    rev49_vertex3_mem rev49_vertex2_mem (by decide)
def rev49_s1_ur : FractionPoint := ⟨40665167099483131,225966663632800000,30858934920432380603739,65384583955468844000000⟩
theorem rev49_s1_ur_mem : rev49_s1_ur.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane66 rev49_vertex3 rev49_vertex2 rev49_s1_ur
    rev49_vertex3_mem rev49_vertex2_mem (by decide)
theorem rev49_slab1 (p : Point) (hp : p∈IntegerCarrier rev49_planes)
    (hx0 : rev49_s1_ll.real.1≤p.1) (hx1 : p.1≤rev49_s1_lr.real.1) :
    p∈rationalHull (fractionRow49.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev49_plane31 rev49_plane66 rev49_s1_ll rev49_s1_lr rev49_s1_ul rev49_s1_ur
    (by decide) rev49_s1_ll_mem rev49_s1_lr_mem rev49_s1_ul_mem rev49_s1_ur_mem p
    (hp _ rev49_plane31_mem) (hp _ rev49_plane66_mem) hx0 hx1
def rev49_s2_ll : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev49_s2_ll_mem : rev49_s2_ll.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane69 rev49_vertex1 rev49_vertex2 rev49_s2_ll
    rev49_vertex1_mem rev49_vertex2_mem (by decide)
def rev49_s2_lr : FractionPoint := ⟨25137957350699011,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev49_s2_lr_mem : rev49_s2_lr.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane69 rev49_vertex1 rev49_vertex2 rev49_s2_lr
    rev49_vertex1_mem rev49_vertex2_mem (by decide)
def rev49_s2_ul : FractionPoint := ⟨40665167099483131,225966663632800000,30858934920432380603739,65384583955468844000000⟩
theorem rev49_s2_ul_mem : rev49_s2_ul.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane66 rev49_vertex3 rev49_vertex2 rev49_s2_ul
    rev49_vertex3_mem rev49_vertex2_mem (by decide)
def rev49_s2_ur : FractionPoint := ⟨25137957350699011,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev49_s2_ur_mem : rev49_s2_ur.real ∈ rationalHull (fractionRow49.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow49 rev49_plane66 rev49_vertex3 rev49_vertex2 rev49_s2_ur
    rev49_vertex3_mem rev49_vertex2_mem (by decide)
theorem rev49_slab2 (p : Point) (hp : p∈IntegerCarrier rev49_planes)
    (hx0 : rev49_s2_ll.real.1≤p.1) (hx1 : p.1≤rev49_s2_lr.real.1) :
    p∈rationalHull (fractionRow49.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev49_plane69 rev49_plane66 rev49_s2_ll rev49_s2_lr rev49_s2_ul rev49_s2_ur
    (by decide) rev49_s2_ll_mem rev49_s2_lr_mem rev49_s2_ul_mem rev49_s2_ur_mem p
    (hp _ rev49_plane69_mem) (hp _ rev49_plane66_mem) hx0 hx1
theorem rev49_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev49_planes) : rev49_s0_ll.real.1≤p.1 := by
  have hc := rev49_plane31.combine_sound rev49_plane45 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev49_plane31_mem) (hp _ rev49_plane45_mem)
  exact (rev49_plane31.combine rev49_plane45 2083356000000 2112760000000).xBoundCheck_sound rev49_s0_ll.nx rev49_s0_ll.dx true (by decide) p hc
theorem rev49_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev49_planes) : p.1≤rev49_s2_lr.real.1 := by
  have hc := rev49_plane66.combine_sound rev49_plane69 16372000000 2083356000000 (by decide) (by decide) p
    (hp _ rev49_plane66_mem) (hp _ rev49_plane69_mem)
  exact (rev49_plane66.combine rev49_plane69 16372000000 2083356000000).xBoundCheck_sound rev49_s2_lr.nx rev49_s2_lr.dx false (by decide) p hc
theorem rev49_hull (p : Point) (hp : p∈IntegerCarrier rev49_planes) :
    p∈rationalHull (fractionRow49.map FractionPoint.rational) := by
  have hxlo := rev49_bound0_lo p hp
  have hxhi := rev49_bound0_hi p hp
  by_cases h0 : p.1≤rev49_s0_lr.real.1
  · exact rev49_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev49_s1_lr.real.1
  · exact rev49_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev49_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull49 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,11,2,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow49 := by
  rw [← fractionRow49_correct]
  exact rev49_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull49
