import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev17_planes : List IntegerPlane := integerOverlayPlanes ![1,2,11,4]
def rev17_plane6 : IntegerPlane := ⟨2083356000000,746024000000,1117516707941⟩
theorem rev17_plane6_mem : rev17_plane6 ∈ rev17_planes := by decide
def rev17_plane9 : IntegerPlane := ⟨(-16372000000),2139440000000,377332847425⟩
theorem rev17_plane9_mem : rev17_plane9 ∈ rev17_planes := by decide
def rev17_plane25 : IntegerPlane := ⟨2083356000000,(-746024000000),965839292059⟩
theorem rev17_plane25_mem : rev17_plane25 ∈ rev17_planes := by decide
def rev17_plane51 : IntegerPlane := ⟨(-2112760000000),48252000000,(-982750749085)⟩
theorem rev17_plane51_mem : rev17_plane51 ∈ rev17_planes := by decide
def rev17_vertex0 : FractionPoint := fractionRow17[0]!
theorem rev17_vertex0_mem : rev17_vertex0∈fractionRow17 := by decide
def rev17_vertex1 : FractionPoint := fractionRow17[1]!
theorem rev17_vertex1_mem : rev17_vertex1∈fractionRow17 := by decide
def rev17_vertex2 : FractionPoint := fractionRow17[2]!
theorem rev17_vertex2_mem : rev17_vertex2∈fractionRow17 := by decide
def rev17_vertex3 : FractionPoint := fractionRow17[3]!
theorem rev17_vertex3_mem : rev17_vertex3∈fractionRow17 := by decide
def rev17_s0_ll : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev17_s0_ll_mem : rev17_s0_ll.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane25 rev17_vertex0 rev17_vertex1 rev17_s0_ll
    rev17_vertex0_mem rev17_vertex1_mem (by decide)
def rev17_s0_lr : FractionPoint := ⟨4241486654352727,9038666545312000,1666052702877665414603,105360346418747492000000⟩
theorem rev17_s0_lr_mem : rev17_s0_lr.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane25 rev17_vertex0 rev17_vertex1 rev17_s0_lr
    rev17_vertex0_mem rev17_vertex1_mem (by decide)
def rev17_s0_ul : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev17_s0_ul_mem : rev17_s0_ul.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane51 rev17_vertex0 rev17_vertex3 rev17_s0_ul
    rev17_vertex0_mem rev17_vertex3_mem (by decide)
def rev17_s0_ur : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev17_s0_ur_mem : rev17_s0_ur.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane51 rev17_vertex0 rev17_vertex3 rev17_s0_ur
    rev17_vertex0_mem rev17_vertex3_mem (by decide)
theorem rev17_slab0 (p : Point) (hp : p∈IntegerCarrier rev17_planes)
    (hx0 : rev17_s0_ll.real.1≤p.1) (hx1 : p.1≤rev17_s0_lr.real.1) :
    p∈rationalHull (fractionRow17.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev17_plane25 rev17_plane51 rev17_s0_ll rev17_s0_lr rev17_s0_ul rev17_s0_ur
    (by decide) rev17_s0_ll_mem rev17_s0_lr_mem rev17_s0_ul_mem rev17_s0_ur_mem p
    (hp _ rev17_plane25_mem) (hp _ rev17_plane51_mem) hx0 hx1
def rev17_s1_ll : FractionPoint := ⟨4241486654352727,9038666545312000,1666052702877665414603,105360346418747492000000⟩
theorem rev17_s1_ll_mem : rev17_s1_ll.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane25 rev17_vertex0 rev17_vertex1 rev17_s1_ll
    rev17_vertex0_mem rev17_vertex1_mem (by decide)
def rev17_s1_lr : FractionPoint := ⟨52734014636747621,111735726639200000,1215606676658188361227,52098458581426588000000⟩
theorem rev17_s1_lr_mem : rev17_s1_lr.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane25 rev17_vertex0 rev17_vertex1 rev17_s1_lr
    rev17_vertex0_mem rev17_vertex1_mem (by decide)
def rev17_s1_ul : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev17_s1_ul_mem : rev17_s1_ul.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane9 rev17_vertex3 rev17_vertex2 rev17_s1_ul
    rev17_vertex3_mem rev17_vertex2_mem (by decide)
def rev17_s1_ur : FractionPoint := ⟨52734014636747621,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev17_s1_ur_mem : rev17_s1_ur.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane9 rev17_vertex3 rev17_vertex2 rev17_s1_ur
    rev17_vertex3_mem rev17_vertex2_mem (by decide)
theorem rev17_slab1 (p : Point) (hp : p∈IntegerCarrier rev17_planes)
    (hx0 : rev17_s1_ll.real.1≤p.1) (hx1 : p.1≤rev17_s1_lr.real.1) :
    p∈rationalHull (fractionRow17.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev17_plane25 rev17_plane9 rev17_s1_ll rev17_s1_lr rev17_s1_ul rev17_s1_ur
    (by decide) rev17_s1_ll_mem rev17_s1_lr_mem rev17_s1_ul_mem rev17_s1_ur_mem p
    (hp _ rev17_plane25_mem) (hp _ rev17_plane9_mem) hx0 hx1
def rev17_s2_ll : FractionPoint := ⟨52734014636747621,111735726639200000,1215606676658188361227,52098458581426588000000⟩
theorem rev17_s2_ll_mem : rev17_s2_ll.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane25 rev17_vertex0 rev17_vertex1 rev17_s2_ll
    rev17_vertex0_mem rev17_vertex1_mem (by decide)
def rev17_s2_lr : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev17_s2_lr_mem : rev17_s2_lr.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane25 rev17_vertex0 rev17_vertex1 rev17_s2_lr
    rev17_vertex0_mem rev17_vertex1_mem (by decide)
def rev17_s2_ul : FractionPoint := ⟨52734014636747621,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev17_s2_ul_mem : rev17_s2_ul.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane6 rev17_vertex2 rev17_vertex1 rev17_s2_ul
    rev17_vertex2_mem rev17_vertex1_mem (by decide)
def rev17_s2_ur : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev17_s2_ur_mem : rev17_s2_ur.real ∈ rationalHull (fractionRow17.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow17 rev17_plane6 rev17_vertex2 rev17_vertex1 rev17_s2_ur
    rev17_vertex2_mem rev17_vertex1_mem (by decide)
theorem rev17_slab2 (p : Point) (hp : p∈IntegerCarrier rev17_planes)
    (hx0 : rev17_s2_ll.real.1≤p.1) (hx1 : p.1≤rev17_s2_lr.real.1) :
    p∈rationalHull (fractionRow17.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev17_plane25 rev17_plane6 rev17_s2_ll rev17_s2_lr rev17_s2_ul rev17_s2_ur
    (by decide) rev17_s2_ll_mem rev17_s2_lr_mem rev17_s2_ul_mem rev17_s2_ur_mem p
    (hp _ rev17_plane25_mem) (hp _ rev17_plane6_mem) hx0 hx1
theorem rev17_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev17_planes) : rev17_s0_ll.real.1≤p.1 := by
  have hc := rev17_plane25.combine_sound rev17_plane51 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev17_plane25_mem) (hp _ rev17_plane51_mem)
  exact (rev17_plane25.combine rev17_plane51 48252000000 746024000000).xBoundCheck_sound rev17_s0_ll.nx rev17_s0_ll.dx true (by decide) p hc
theorem rev17_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev17_planes) : p.1≤rev17_s2_lr.real.1 := by
  have hc := rev17_plane6.combine_sound rev17_plane25 746024000000 746024000000 (by decide) (by decide) p
    (hp _ rev17_plane6_mem) (hp _ rev17_plane25_mem)
  exact (rev17_plane6.combine rev17_plane25 746024000000 746024000000).xBoundCheck_sound rev17_s2_lr.nx rev17_s2_lr.dx false (by decide) p hc
theorem rev17_hull (p : Point) (hp : p∈IntegerCarrier rev17_planes) :
    p∈rationalHull (fractionRow17.map FractionPoint.rational) := by
  have hxlo := rev17_bound0_lo p hp
  have hxhi := rev17_bound0_hi p hp
  by_cases h0 : p.1≤rev17_s0_lr.real.1
  · exact rev17_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev17_s1_lr.real.1
  · exact rev17_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev17_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull17 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,2,11,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow17 := by
  rw [← fractionRow17_correct]
  exact rev17_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull17
