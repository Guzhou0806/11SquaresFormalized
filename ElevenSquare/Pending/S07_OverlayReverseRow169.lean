import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev169_planes : List IntegerPlane := integerOverlayPlanes ![11,4,13,13]
def rev169_plane54 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-2133599860516)⟩
theorem rev169_plane54_mem : rev169_plane54 ∈ rev169_planes := by decide
def rev169_plane58 : IntegerPlane := ⟨746024000000,(-2083356000000),(-371492707941)⟩
theorem rev169_plane58_mem : rev169_plane58 ∈ rev169_planes := by decide
def rev169_plane74 : IntegerPlane := ⟨(-1393416000000),2099728000000,(-33871860516)⟩
theorem rev169_plane74_mem : rev169_plane74 ∈ rev169_planes := by decide
def rev169_plane78 : IntegerPlane := ⟨746024000000,2083356000000,1711863292059⟩
theorem rev169_plane78_mem : rev169_plane78 ∈ rev169_planes := by decide
def rev169_vertex0 : FractionPoint := fractionRow169[0]!
theorem rev169_vertex0_mem : rev169_vertex0∈fractionRow169 := by decide
def rev169_vertex1 : FractionPoint := fractionRow169[1]!
theorem rev169_vertex1_mem : rev169_vertex1∈fractionRow169 := by decide
def rev169_vertex2 : FractionPoint := fractionRow169[2]!
theorem rev169_vertex2_mem : rev169_vertex2∈fractionRow169 := by decide
def rev169_vertex3 : FractionPoint := fractionRow169[3]!
theorem rev169_vertex3_mem : rev169_vertex3∈fractionRow169 := by decide
def rev169_s0_ll : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev169_s0_ll_mem : rev169_s0_ll.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane54 rev169_vertex1 rev169_vertex2 rev169_s0_ll
    rev169_vertex1_mem rev169_vertex2_mem (by decide)
def rev169_s0_lr : FractionPoint := ⟨114531700948300989,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev169_s0_lr_mem : rev169_s0_lr.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane54 rev169_vertex1 rev169_vertex2 rev169_s0_lr
    rev169_vertex1_mem rev169_vertex2_mem (by decide)
def rev169_s0_ul : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev169_s0_ul_mem : rev169_s0_ul.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane74 rev169_vertex1 rev169_vertex0 rev169_s0_ul
    rev169_vertex1_mem rev169_vertex0_mem (by decide)
def rev169_s0_ur : FractionPoint := ⟨114531700948300989,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev169_s0_ur_mem : rev169_s0_ur.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane74 rev169_vertex1 rev169_vertex0 rev169_s0_ur
    rev169_vertex1_mem rev169_vertex0_mem (by decide)
theorem rev169_slab0 (p : Point) (hp : p∈IntegerCarrier rev169_planes)
    (hx0 : rev169_s0_ll.real.1≤p.1) (hx1 : p.1≤rev169_s0_lr.real.1) :
    p∈rationalHull (fractionRow169.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev169_plane54 rev169_plane74 rev169_s0_ll rev169_s0_lr rev169_s0_ul rev169_s0_ur
    (by decide) rev169_s0_ll_mem rev169_s0_lr_mem rev169_s0_ul_mem rev169_s0_ur_mem p
    (hp _ rev169_plane54_mem) (hp _ rev169_plane74_mem) hx0 hx1
def rev169_s1_ll : FractionPoint := ⟨114531700948300989,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev169_s1_ll_mem : rev169_s1_ll.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane58 rev169_vertex2 rev169_vertex3 rev169_s1_ll
    rev169_vertex2_mem rev169_vertex3_mem (by decide)
def rev169_s1_lr : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev169_s1_lr_mem : rev169_s1_lr.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane58 rev169_vertex2 rev169_vertex3 rev169_s1_lr
    rev169_vertex2_mem rev169_vertex3_mem (by decide)
def rev169_s1_ul : FractionPoint := ⟨114531700948300989,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev169_s1_ul_mem : rev169_s1_ul.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane78 rev169_vertex0 rev169_vertex3 rev169_s1_ul
    rev169_vertex0_mem rev169_vertex3_mem (by decide)
def rev169_s1_ur : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev169_s1_ur_mem : rev169_s1_ur.real ∈ rationalHull (fractionRow169.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow169 rev169_plane78 rev169_vertex0 rev169_vertex3 rev169_s1_ur
    rev169_vertex0_mem rev169_vertex3_mem (by decide)
theorem rev169_slab1 (p : Point) (hp : p∈IntegerCarrier rev169_planes)
    (hx0 : rev169_s1_ll.real.1≤p.1) (hx1 : p.1≤rev169_s1_lr.real.1) :
    p∈rationalHull (fractionRow169.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev169_plane58 rev169_plane78 rev169_s1_ll rev169_s1_lr rev169_s1_ul rev169_s1_ur
    (by decide) rev169_s1_ll_mem rev169_s1_lr_mem rev169_s1_ul_mem rev169_s1_ur_mem p
    (hp _ rev169_plane58_mem) (hp _ rev169_plane78_mem) hx0 hx1
theorem rev169_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev169_planes) : rev169_s0_ll.real.1≤p.1 := by
  have hc := rev169_plane54.combine_sound rev169_plane74 2099728000000 2099728000000 (by decide) (by decide) p
    (hp _ rev169_plane54_mem) (hp _ rev169_plane74_mem)
  exact (rev169_plane54.combine rev169_plane74 2099728000000 2099728000000).xBoundCheck_sound rev169_s0_ll.nx rev169_s0_ll.dx true (by decide) p hc
theorem rev169_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev169_planes) : p.1≤rev169_s1_lr.real.1 := by
  have hc := rev169_plane58.combine_sound rev169_plane78 2083356000000 2083356000000 (by decide) (by decide) p
    (hp _ rev169_plane58_mem) (hp _ rev169_plane78_mem)
  exact (rev169_plane58.combine rev169_plane78 2083356000000 2083356000000).xBoundCheck_sound rev169_s1_lr.nx rev169_s1_lr.dx false (by decide) p hc
theorem rev169_hull (p : Point) (hp : p∈IntegerCarrier rev169_planes) :
    p∈rationalHull (fractionRow169.map FractionPoint.rational) := by
  have hxlo := rev169_bound0_lo p hp
  have hxhi := rev169_bound0_hi p hp
  by_cases h0 : p.1≤rev169_s0_lr.real.1
  · exact rev169_slab0 p hp hxlo h0
  exact rev169_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull169 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,4,13,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow169 := by
  rw [← fractionRow169_correct]
  exact rev169_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull169
