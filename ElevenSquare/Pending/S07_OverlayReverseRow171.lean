import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev171_planes : List IntegerPlane := integerOverlayPlanes ![11,4,14,13]
def rev171_plane11 : IntegerPlane := ⟨(-48252000000),(-2112760000000),(-1031002749085)⟩
theorem rev171_plane11_mem : rev171_plane11 ∈ rev171_planes := by decide
def rev171_plane54 : IntegerPlane := ⟨(-2139440000000),(-16372000000),(-1762107152575)⟩
theorem rev171_plane54_mem : rev171_plane54 ∈ rev171_planes := by decide
def rev171_plane57 : IntegerPlane := ⟨(-746024000000),2083356000000,371492707941⟩
theorem rev171_plane57_mem : rev171_plane57 ∈ rev171_planes := by decide
def rev171_plane78 : IntegerPlane := ⟨746024000000,2083356000000,1711863292059⟩
theorem rev171_plane78_mem : rev171_plane78 ∈ rev171_planes := by decide
def rev171_vertex0 : FractionPoint := fractionRow171[0]!
theorem rev171_vertex0_mem : rev171_vertex0∈fractionRow171 := by decide
def rev171_vertex1 : FractionPoint := fractionRow171[1]!
theorem rev171_vertex1_mem : rev171_vertex1∈fractionRow171 := by decide
def rev171_vertex2 : FractionPoint := fractionRow171[2]!
theorem rev171_vertex2_mem : rev171_vertex2∈fractionRow171 := by decide
def rev171_vertex3 : FractionPoint := fractionRow171[3]!
theorem rev171_vertex3_mem : rev171_vertex3∈fractionRow171 := by decide
def rev171_s0_ll : FractionPoint := ⟨114531700948300989,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev171_s0_ll_mem : rev171_s0_ll.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane54 rev171_vertex1 rev171_vertex2 rev171_s0_ll
    rev171_vertex1_mem rev171_vertex2_mem (by decide)
def rev171_s0_lr : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev171_s0_lr_mem : rev171_s0_lr.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane54 rev171_vertex1 rev171_vertex2 rev171_s0_lr
    rev171_vertex1_mem rev171_vertex2_mem (by decide)
def rev171_s0_ul : FractionPoint := ⟨114531700948300989,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev171_s0_ul_mem : rev171_s0_ul.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane57 rev171_vertex1 rev171_vertex0 rev171_s0_ul
    rev171_vertex1_mem rev171_vertex0_mem (by decide)
def rev171_s0_ur : FractionPoint := ⟨185301496533316869,225966663632800000,30858934920432380603739,65384583955468844000000⟩
theorem rev171_s0_ur_mem : rev171_s0_ur.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane57 rev171_vertex1 rev171_vertex0 rev171_s0_ur
    rev171_vertex1_mem rev171_vertex0_mem (by decide)
theorem rev171_slab0 (p : Point) (hp : p∈IntegerCarrier rev171_planes)
    (hx0 : rev171_s0_ll.real.1≤p.1) (hx1 : p.1≤rev171_s0_lr.real.1) :
    p∈rationalHull (fractionRow171.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev171_plane54 rev171_plane57 rev171_s0_ll rev171_s0_lr rev171_s0_ul rev171_s0_ur
    (by decide) rev171_s0_ll_mem rev171_s0_lr_mem rev171_s0_ul_mem rev171_s0_ur_mem p
    (hp _ rev171_plane54_mem) (hp _ rev171_plane57_mem) hx0 hx1
def rev171_s1_ll : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev171_s1_ll_mem : rev171_s1_ll.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane11 rev171_vertex2 rev171_vertex3 rev171_s1_ll
    rev171_vertex2_mem rev171_vertex3_mem (by decide)
def rev171_s1_lr : FractionPoint := ⟨670185292059,746024000000,184203753542739293,394042416560000000⟩
theorem rev171_s1_lr_mem : rev171_s1_lr.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane11 rev171_vertex2 rev171_vertex3 rev171_s1_lr
    rev171_vertex2_mem rev171_vertex3_mem (by decide)
def rev171_s1_ul : FractionPoint := ⟨185301496533316869,225966663632800000,30858934920432380603739,65384583955468844000000⟩
theorem rev171_s1_ul_mem : rev171_s1_ul.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane57 rev171_vertex1 rev171_vertex0 rev171_s1_ul
    rev171_vertex1_mem rev171_vertex0_mem (by decide)
def rev171_s1_ur : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev171_s1_ur_mem : rev171_s1_ur.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane57 rev171_vertex1 rev171_vertex0 rev171_s1_ur
    rev171_vertex1_mem rev171_vertex0_mem (by decide)
theorem rev171_slab1 (p : Point) (hp : p∈IntegerCarrier rev171_planes)
    (hx0 : rev171_s1_ll.real.1≤p.1) (hx1 : p.1≤rev171_s1_lr.real.1) :
    p∈rationalHull (fractionRow171.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev171_plane11 rev171_plane57 rev171_s1_ll rev171_s1_lr rev171_s1_ul rev171_s1_ur
    (by decide) rev171_s1_ll_mem rev171_s1_lr_mem rev171_s1_ul_mem rev171_s1_ur_mem p
    (hp _ rev171_plane11_mem) (hp _ rev171_plane57_mem) hx0 hx1
def rev171_s2_ll : FractionPoint := ⟨670185292059,746024000000,184203753542739293,394042416560000000⟩
theorem rev171_s2_ll_mem : rev171_s2_ll.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane11 rev171_vertex2 rev171_vertex3 rev171_s2_ll
    rev171_vertex2_mem rev171_vertex3_mem (by decide)
def rev171_s2_lr : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev171_s2_lr_mem : rev171_s2_lr.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane11 rev171_vertex2 rev171_vertex3 rev171_s2_lr
    rev171_vertex2_mem rev171_vertex3_mem (by decide)
def rev171_s2_ul : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev171_s2_ul_mem : rev171_s2_ul.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane78 rev171_vertex0 rev171_vertex3 rev171_s2_ul
    rev171_vertex0_mem rev171_vertex3_mem (by decide)
def rev171_s2_ur : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev171_s2_ur_mem : rev171_s2_ur.real ∈ rationalHull (fractionRow171.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow171 rev171_plane78 rev171_vertex0 rev171_vertex3 rev171_s2_ur
    rev171_vertex0_mem rev171_vertex3_mem (by decide)
theorem rev171_slab2 (p : Point) (hp : p∈IntegerCarrier rev171_planes)
    (hx0 : rev171_s2_ll.real.1≤p.1) (hx1 : p.1≤rev171_s2_lr.real.1) :
    p∈rationalHull (fractionRow171.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev171_plane11 rev171_plane78 rev171_s2_ll rev171_s2_lr rev171_s2_ul rev171_s2_ur
    (by decide) rev171_s2_ll_mem rev171_s2_lr_mem rev171_s2_ul_mem rev171_s2_ur_mem p
    (hp _ rev171_plane11_mem) (hp _ rev171_plane78_mem) hx0 hx1
theorem rev171_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev171_planes) : rev171_s0_ll.real.1≤p.1 := by
  have hc := rev171_plane54.combine_sound rev171_plane57 2083356000000 16372000000 (by decide) (by decide) p
    (hp _ rev171_plane54_mem) (hp _ rev171_plane57_mem)
  exact (rev171_plane54.combine rev171_plane57 2083356000000 16372000000).xBoundCheck_sound rev171_s0_ll.nx rev171_s0_ll.dx true (by decide) p hc
theorem rev171_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev171_planes) : p.1≤rev171_s2_lr.real.1 := by
  have hc := rev171_plane11.combine_sound rev171_plane78 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev171_plane11_mem) (hp _ rev171_plane78_mem)
  exact (rev171_plane11.combine rev171_plane78 2083356000000 2112760000000).xBoundCheck_sound rev171_s2_lr.nx rev171_s2_lr.dx false (by decide) p hc
theorem rev171_hull (p : Point) (hp : p∈IntegerCarrier rev171_planes) :
    p∈rationalHull (fractionRow171.map FractionPoint.rational) := by
  have hxlo := rev171_bound0_lo p hp
  have hxhi := rev171_bound0_hi p hp
  by_cases h0 : p.1≤rev171_s0_lr.real.1
  · exact rev171_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev171_s1_lr.real.1
  · exact rev171_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev171_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull171 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,4,14,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow171 := by
  rw [← fractionRow171_correct]
  exact rev171_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull171
