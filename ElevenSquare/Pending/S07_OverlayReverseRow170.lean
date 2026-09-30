import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev170_planes : List IntegerPlane := integerOverlayPlanes ![11,4,13,14]
def rev170_plane32 : IntegerPlane := ⟨(-48252000000),2112760000000,1081757250915⟩
theorem rev170_plane32_mem : rev170_plane32 ∈ rev170_planes := by decide
def rev170_plane58 : IntegerPlane := ⟨746024000000,(-2083356000000),(-371492707941)⟩
theorem rev170_plane58_mem : rev170_plane58 ∈ rev170_planes := by decide
def rev170_plane74 : IntegerPlane := ⟨(-2139440000000),16372000000,(-1745735152575)⟩
theorem rev170_plane74_mem : rev170_plane74 ∈ rev170_planes := by decide
def rev170_plane77 : IntegerPlane := ⟨(-746024000000),(-2083356000000),(-1711863292059)⟩
theorem rev170_plane77_mem : rev170_plane77 ∈ rev170_planes := by decide
def rev170_vertex0 : FractionPoint := fractionRow170[0]!
theorem rev170_vertex0_mem : rev170_vertex0∈fractionRow170 := by decide
def rev170_vertex1 : FractionPoint := fractionRow170[1]!
theorem rev170_vertex1_mem : rev170_vertex1∈fractionRow170 := by decide
def rev170_vertex2 : FractionPoint := fractionRow170[2]!
theorem rev170_vertex2_mem : rev170_vertex2∈fractionRow170 := by decide
def rev170_vertex3 : FractionPoint := fractionRow170[3]!
theorem rev170_vertex3_mem : rev170_vertex3∈fractionRow170 := by decide
def rev170_s0_ll : FractionPoint := ⟨114531700948300989,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev170_s0_ll_mem : rev170_s0_ll.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane77 rev170_vertex2 rev170_vertex3 rev170_s0_ll
    rev170_vertex2_mem rev170_vertex3_mem (by decide)
def rev170_s0_lr : FractionPoint := ⟨185301496533316869,225966663632800000,34525649035036463396261,65384583955468844000000⟩
theorem rev170_s0_lr_mem : rev170_s0_lr.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane77 rev170_vertex2 rev170_vertex3 rev170_s0_lr
    rev170_vertex2_mem rev170_vertex3_mem (by decide)
def rev170_s0_ul : FractionPoint := ⟨114531700948300989,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev170_s0_ul_mem : rev170_s0_ul.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane74 rev170_vertex2 rev170_vertex1 rev170_s0_ul
    rev170_vertex2_mem rev170_vertex1_mem (by decide)
def rev170_s0_ur : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev170_s0_ur_mem : rev170_s0_ur.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane74 rev170_vertex2 rev170_vertex1 rev170_s0_ur
    rev170_vertex2_mem rev170_vertex1_mem (by decide)
theorem rev170_slab0 (p : Point) (hp : p∈IntegerCarrier rev170_planes)
    (hx0 : rev170_s0_ll.real.1≤p.1) (hx1 : p.1≤rev170_s0_lr.real.1) :
    p∈rationalHull (fractionRow170.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev170_plane77 rev170_plane74 rev170_s0_ll rev170_s0_lr rev170_s0_ul rev170_s0_ur
    (by decide) rev170_s0_ll_mem rev170_s0_lr_mem rev170_s0_ul_mem rev170_s0_ur_mem p
    (hp _ rev170_plane77_mem) (hp _ rev170_plane74_mem) hx0 hx1
def rev170_s1_ll : FractionPoint := ⟨185301496533316869,225966663632800000,34525649035036463396261,65384583955468844000000⟩
theorem rev170_s1_ll_mem : rev170_s1_ll.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane77 rev170_vertex2 rev170_vertex3 rev170_s1_ll
    rev170_vertex2_mem rev170_vertex3_mem (by decide)
def rev170_s1_lr : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev170_s1_lr_mem : rev170_s1_lr.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane77 rev170_vertex2 rev170_vertex3 rev170_s1_lr
    rev170_vertex2_mem rev170_vertex3_mem (by decide)
def rev170_s1_ul : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev170_s1_ul_mem : rev170_s1_ul.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane32 rev170_vertex1 rev170_vertex0 rev170_s1_ul
    rev170_vertex1_mem rev170_vertex0_mem (by decide)
def rev170_s1_ur : FractionPoint := ⟨670185292059,746024000000,209838663017260707,394042416560000000⟩
theorem rev170_s1_ur_mem : rev170_s1_ur.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane32 rev170_vertex1 rev170_vertex0 rev170_s1_ur
    rev170_vertex1_mem rev170_vertex0_mem (by decide)
theorem rev170_slab1 (p : Point) (hp : p∈IntegerCarrier rev170_planes)
    (hx0 : rev170_s1_ll.real.1≤p.1) (hx1 : p.1≤rev170_s1_lr.real.1) :
    p∈rationalHull (fractionRow170.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev170_plane77 rev170_plane32 rev170_s1_ll rev170_s1_lr rev170_s1_ul rev170_s1_ur
    (by decide) rev170_s1_ll_mem rev170_s1_lr_mem rev170_s1_ul_mem rev170_s1_ur_mem p
    (hp _ rev170_plane77_mem) (hp _ rev170_plane32_mem) hx0 hx1
def rev170_s2_ll : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev170_s2_ll_mem : rev170_s2_ll.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane58 rev170_vertex3 rev170_vertex0 rev170_s2_ll
    rev170_vertex3_mem rev170_vertex0_mem (by decide)
def rev170_s2_lr : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev170_s2_lr_mem : rev170_s2_lr.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane58 rev170_vertex3 rev170_vertex0 rev170_s2_lr
    rev170_vertex3_mem rev170_vertex0_mem (by decide)
def rev170_s2_ul : FractionPoint := ⟨670185292059,746024000000,209838663017260707,394042416560000000⟩
theorem rev170_s2_ul_mem : rev170_s2_ul.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane32 rev170_vertex1 rev170_vertex0 rev170_s2_ul
    rev170_vertex1_mem rev170_vertex0_mem (by decide)
def rev170_s2_ur : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev170_s2_ur_mem : rev170_s2_ur.real ∈ rationalHull (fractionRow170.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow170 rev170_plane32 rev170_vertex1 rev170_vertex0 rev170_s2_ur
    rev170_vertex1_mem rev170_vertex0_mem (by decide)
theorem rev170_slab2 (p : Point) (hp : p∈IntegerCarrier rev170_planes)
    (hx0 : rev170_s2_ll.real.1≤p.1) (hx1 : p.1≤rev170_s2_lr.real.1) :
    p∈rationalHull (fractionRow170.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev170_plane58 rev170_plane32 rev170_s2_ll rev170_s2_lr rev170_s2_ul rev170_s2_ur
    (by decide) rev170_s2_ll_mem rev170_s2_lr_mem rev170_s2_ul_mem rev170_s2_ur_mem p
    (hp _ rev170_plane58_mem) (hp _ rev170_plane32_mem) hx0 hx1
theorem rev170_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev170_planes) : rev170_s0_ll.real.1≤p.1 := by
  have hc := rev170_plane74.combine_sound rev170_plane77 2083356000000 16372000000 (by decide) (by decide) p
    (hp _ rev170_plane74_mem) (hp _ rev170_plane77_mem)
  exact (rev170_plane74.combine rev170_plane77 2083356000000 16372000000).xBoundCheck_sound rev170_s0_ll.nx rev170_s0_ll.dx true (by decide) p hc
theorem rev170_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev170_planes) : p.1≤rev170_s2_lr.real.1 := by
  have hc := rev170_plane32.combine_sound rev170_plane58 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev170_plane32_mem) (hp _ rev170_plane58_mem)
  exact (rev170_plane32.combine rev170_plane58 2083356000000 2112760000000).xBoundCheck_sound rev170_s2_lr.nx rev170_s2_lr.dx false (by decide) p hc
theorem rev170_hull (p : Point) (hp : p∈IntegerCarrier rev170_planes) :
    p∈rationalHull (fractionRow170.map FractionPoint.rational) := by
  have hxlo := rev170_bound0_lo p hp
  have hxhi := rev170_bound0_hi p hp
  by_cases h0 : p.1≤rev170_s0_lr.real.1
  · exact rev170_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev170_s1_lr.real.1
  · exact rev170_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev170_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull170 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,4,13,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow170 := by
  rw [← fractionRow170_correct]
  exact rev170_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull170
