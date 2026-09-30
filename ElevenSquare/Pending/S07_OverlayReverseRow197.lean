import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev197_planes : List IntegerPlane := integerOverlayPlanes ![13,14,4,11]
def rev197_plane18 : IntegerPlane := ⟨2083356000000,746024000000,1711863292059⟩
theorem rev197_plane18_mem : rev197_plane18 ∈ rev197_planes := by decide
def rev197_plane34 : IntegerPlane := ⟨(-16372000000),(-2139440000000),(-1762107152575)⟩
theorem rev197_plane34_mem : rev197_plane34 ∈ rev197_planes := by decide
def rev197_plane37 : IntegerPlane := ⟨2083356000000,(-746024000000),371492707941⟩
theorem rev197_plane37_mem : rev197_plane37 ∈ rev197_planes := by decide
def rev197_plane71 : IntegerPlane := ⟨(-2112760000000),(-48252000000),(-1031002749085)⟩
theorem rev197_plane71_mem : rev197_plane71 ∈ rev197_planes := by decide
def rev197_vertex0 : FractionPoint := fractionRow197[0]!
theorem rev197_vertex0_mem : rev197_vertex0∈fractionRow197 := by decide
def rev197_vertex1 : FractionPoint := fractionRow197[1]!
theorem rev197_vertex1_mem : rev197_vertex1∈fractionRow197 := by decide
def rev197_vertex2 : FractionPoint := fractionRow197[2]!
theorem rev197_vertex2_mem : rev197_vertex2∈fractionRow197 := by decide
def rev197_vertex3 : FractionPoint := fractionRow197[3]!
theorem rev197_vertex3_mem : rev197_vertex3∈fractionRow197 := by decide
def rev197_s0_ll : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev197_s0_ll_mem : rev197_s0_ll.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane71 rev197_vertex3 rev197_vertex0 rev197_s0_ll
    rev197_vertex3_mem rev197_vertex0_mem (by decide)
def rev197_s0_lr : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev197_s0_lr_mem : rev197_s0_lr.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane71 rev197_vertex3 rev197_vertex0 rev197_s0_lr
    rev197_vertex3_mem rev197_vertex0_mem (by decide)
def rev197_s0_ul : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev197_s0_ul_mem : rev197_s0_ul.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane18 rev197_vertex3 rev197_vertex2 rev197_s0_ul
    rev197_vertex3_mem rev197_vertex2_mem (by decide)
def rev197_s0_ur : FractionPoint := ⟨4241486654352727,9038666545312000,103694293715869826585397,105360346418747492000000⟩
theorem rev197_s0_ur_mem : rev197_s0_ur.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane18 rev197_vertex3 rev197_vertex2 rev197_s0_ur
    rev197_vertex3_mem rev197_vertex2_mem (by decide)
theorem rev197_slab0 (p : Point) (hp : p∈IntegerCarrier rev197_planes)
    (hx0 : rev197_s0_ll.real.1≤p.1) (hx1 : p.1≤rev197_s0_lr.real.1) :
    p∈rationalHull (fractionRow197.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev197_plane71 rev197_plane18 rev197_s0_ll rev197_s0_lr rev197_s0_ul rev197_s0_ur
    (by decide) rev197_s0_ll_mem rev197_s0_lr_mem rev197_s0_ul_mem rev197_s0_ur_mem p
    (hp _ rev197_plane71_mem) (hp _ rev197_plane18_mem) hx0 hx1
def rev197_s1_ll : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev197_s1_ll_mem : rev197_s1_ll.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane34 rev197_vertex0 rev197_vertex1 rev197_s1_ll
    rev197_vertex0_mem rev197_vertex1_mem (by decide)
def rev197_s1_lr : FractionPoint := ⟨52734014636747621,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev197_s1_lr_mem : rev197_s1_lr.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane34 rev197_vertex0 rev197_vertex1 rev197_s1_lr
    rev197_vertex0_mem rev197_vertex1_mem (by decide)
def rev197_s1_ul : FractionPoint := ⟨4241486654352727,9038666545312000,103694293715869826585397,105360346418747492000000⟩
theorem rev197_s1_ul_mem : rev197_s1_ul.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane18 rev197_vertex3 rev197_vertex2 rev197_s1_ul
    rev197_vertex3_mem rev197_vertex2_mem (by decide)
def rev197_s1_ur : FractionPoint := ⟨52734014636747621,111735726639200000,50882851904768399638773,52098458581426588000000⟩
theorem rev197_s1_ur_mem : rev197_s1_ur.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane18 rev197_vertex3 rev197_vertex2 rev197_s1_ur
    rev197_vertex3_mem rev197_vertex2_mem (by decide)
theorem rev197_slab1 (p : Point) (hp : p∈IntegerCarrier rev197_planes)
    (hx0 : rev197_s1_ll.real.1≤p.1) (hx1 : p.1≤rev197_s1_lr.real.1) :
    p∈rationalHull (fractionRow197.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev197_plane34 rev197_plane18 rev197_s1_ll rev197_s1_lr rev197_s1_ul rev197_s1_ur
    (by decide) rev197_s1_ll_mem rev197_s1_lr_mem rev197_s1_ul_mem rev197_s1_ur_mem p
    (hp _ rev197_plane34_mem) (hp _ rev197_plane18_mem) hx0 hx1
def rev197_s2_ll : FractionPoint := ⟨52734014636747621,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev197_s2_ll_mem : rev197_s2_ll.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane37 rev197_vertex1 rev197_vertex2 rev197_s2_ll
    rev197_vertex1_mem rev197_vertex2_mem (by decide)
def rev197_s2_lr : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev197_s2_lr_mem : rev197_s2_lr.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane37 rev197_vertex1 rev197_vertex2 rev197_s2_lr
    rev197_vertex1_mem rev197_vertex2_mem (by decide)
def rev197_s2_ul : FractionPoint := ⟨52734014636747621,111735726639200000,50882851904768399638773,52098458581426588000000⟩
theorem rev197_s2_ul_mem : rev197_s2_ul.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane18 rev197_vertex3 rev197_vertex2 rev197_s2_ul
    rev197_vertex3_mem rev197_vertex2_mem (by decide)
def rev197_s2_ur : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev197_s2_ur_mem : rev197_s2_ur.real ∈ rationalHull (fractionRow197.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow197 rev197_plane18 rev197_vertex3 rev197_vertex2 rev197_s2_ur
    rev197_vertex3_mem rev197_vertex2_mem (by decide)
theorem rev197_slab2 (p : Point) (hp : p∈IntegerCarrier rev197_planes)
    (hx0 : rev197_s2_ll.real.1≤p.1) (hx1 : p.1≤rev197_s2_lr.real.1) :
    p∈rationalHull (fractionRow197.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev197_plane37 rev197_plane18 rev197_s2_ll rev197_s2_lr rev197_s2_ul rev197_s2_ur
    (by decide) rev197_s2_ll_mem rev197_s2_lr_mem rev197_s2_ul_mem rev197_s2_ur_mem p
    (hp _ rev197_plane37_mem) (hp _ rev197_plane18_mem) hx0 hx1
theorem rev197_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev197_planes) : rev197_s0_ll.real.1≤p.1 := by
  have hc := rev197_plane18.combine_sound rev197_plane71 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev197_plane18_mem) (hp _ rev197_plane71_mem)
  exact (rev197_plane18.combine rev197_plane71 48252000000 746024000000).xBoundCheck_sound rev197_s0_ll.nx rev197_s0_ll.dx true (by decide) p hc
theorem rev197_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev197_planes) : p.1≤rev197_s2_lr.real.1 := by
  have hc := rev197_plane18.combine_sound rev197_plane37 746024000000 746024000000 (by decide) (by decide) p
    (hp _ rev197_plane18_mem) (hp _ rev197_plane37_mem)
  exact (rev197_plane18.combine rev197_plane37 746024000000 746024000000).xBoundCheck_sound rev197_s2_lr.nx rev197_s2_lr.dx false (by decide) p hc
theorem rev197_hull (p : Point) (hp : p∈IntegerCarrier rev197_planes) :
    p∈rationalHull (fractionRow197.map FractionPoint.rational) := by
  have hxlo := rev197_bound0_lo p hp
  have hxhi := rev197_bound0_hi p hp
  by_cases h0 : p.1≤rev197_s0_lr.real.1
  · exact rev197_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev197_s1_lr.real.1
  · exact rev197_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev197_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull197 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,14,4,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow197 := by
  rw [← fractionRow197_correct]
  exact rev197_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull197
