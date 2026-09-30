import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev172_planes : List IntegerPlane := integerOverlayPlanes ![11,4,14,14]
def rev172_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev172_plane1_mem : rev172_plane1 ∈ rev172_planes := by decide
def rev172_plane11 : IntegerPlane := ⟨(-48252000000),(-2112760000000),(-1031002749085)⟩
theorem rev172_plane11_mem : rev172_plane11 ∈ rev172_planes := by decide
def rev172_plane32 : IntegerPlane := ⟨(-48252000000),2112760000000,1081757250915⟩
theorem rev172_plane32_mem : rev172_plane32 ∈ rev172_planes := by decide
def rev172_plane57 : IntegerPlane := ⟨(-746024000000),2083356000000,371492707941⟩
theorem rev172_plane57_mem : rev172_plane57 ∈ rev172_planes := by decide
def rev172_plane77 : IntegerPlane := ⟨(-746024000000),(-2083356000000),(-1711863292059)⟩
theorem rev172_plane77_mem : rev172_plane77 ∈ rev172_planes := by decide
def rev172_vertex0 : FractionPoint := fractionRow172[0]!
theorem rev172_vertex0_mem : rev172_vertex0∈fractionRow172 := by decide
def rev172_vertex1 : FractionPoint := fractionRow172[1]!
theorem rev172_vertex1_mem : rev172_vertex1∈fractionRow172 := by decide
def rev172_vertex2 : FractionPoint := fractionRow172[2]!
theorem rev172_vertex2_mem : rev172_vertex2∈fractionRow172 := by decide
def rev172_vertex3 : FractionPoint := fractionRow172[3]!
theorem rev172_vertex3_mem : rev172_vertex3∈fractionRow172 := by decide
def rev172_vertex4 : FractionPoint := fractionRow172[4]!
theorem rev172_vertex4_mem : rev172_vertex4∈fractionRow172 := by decide
def rev172_s0_ll : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev172_s0_ll_mem : rev172_s0_ll.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane77 rev172_vertex3 rev172_vertex4 rev172_s0_ll
    rev172_vertex3_mem rev172_vertex4_mem (by decide)
def rev172_s0_lr : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev172_s0_lr_mem : rev172_s0_lr.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane77 rev172_vertex3 rev172_vertex4 rev172_s0_lr
    rev172_vertex3_mem rev172_vertex4_mem (by decide)
def rev172_s0_ul : FractionPoint := ⟨670185292059,746024000000,1,2⟩
theorem rev172_s0_ul_mem : rev172_s0_ul.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane57 rev172_vertex3 rev172_vertex2 rev172_s0_ul
    rev172_vertex3_mem rev172_vertex2_mem (by decide)
def rev172_s0_ur : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev172_s0_ur_mem : rev172_s0_ur.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane57 rev172_vertex3 rev172_vertex2 rev172_s0_ur
    rev172_vertex3_mem rev172_vertex2_mem (by decide)
theorem rev172_slab0 (p : Point) (hp : p∈IntegerCarrier rev172_planes)
    (hx0 : rev172_s0_ll.real.1≤p.1) (hx1 : p.1≤rev172_s0_lr.real.1) :
    p∈rationalHull (fractionRow172.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev172_plane77 rev172_plane57 rev172_s0_ll rev172_s0_lr rev172_s0_ul rev172_s0_ur
    (by decide) rev172_s0_ll_mem rev172_s0_lr_mem rev172_s0_ul_mem rev172_s0_ur_mem p
    (hp _ rev172_plane77_mem) (hp _ rev172_plane57_mem) hx0 hx1
def rev172_s1_ll : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev172_s1_ll_mem : rev172_s1_ll.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane11 rev172_vertex4 rev172_vertex0 rev172_s1_ll
    rev172_vertex4_mem rev172_vertex0_mem (by decide)
def rev172_s1_lr : FractionPoint := ⟨1,1,196550149817,422552000000⟩
theorem rev172_s1_lr_mem : rev172_s1_lr.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane11 rev172_vertex4 rev172_vertex0 rev172_s1_lr
    rev172_vertex4_mem rev172_vertex0_mem (by decide)
def rev172_s1_ul : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev172_s1_ul_mem : rev172_s1_ul.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane32 rev172_vertex2 rev172_vertex1 rev172_s1_ul
    rev172_vertex2_mem rev172_vertex1_mem (by decide)
def rev172_s1_ur : FractionPoint := ⟨1,1,226001850183,422552000000⟩
theorem rev172_s1_ur_mem : rev172_s1_ur.real ∈ rationalHull (fractionRow172.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow172 rev172_plane32 rev172_vertex2 rev172_vertex1 rev172_s1_ur
    rev172_vertex2_mem rev172_vertex1_mem (by decide)
theorem rev172_slab1 (p : Point) (hp : p∈IntegerCarrier rev172_planes)
    (hx0 : rev172_s1_ll.real.1≤p.1) (hx1 : p.1≤rev172_s1_lr.real.1) :
    p∈rationalHull (fractionRow172.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev172_plane11 rev172_plane32 rev172_s1_ll rev172_s1_lr rev172_s1_ul rev172_s1_ur
    (by decide) rev172_s1_ll_mem rev172_s1_lr_mem rev172_s1_ul_mem rev172_s1_ur_mem p
    (hp _ rev172_plane11_mem) (hp _ rev172_plane32_mem) hx0 hx1
theorem rev172_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev172_planes) : rev172_s0_ll.real.1≤p.1 := by
  have hc := rev172_plane57.combine_sound rev172_plane77 2083356000000 2083356000000 (by decide) (by decide) p
    (hp _ rev172_plane57_mem) (hp _ rev172_plane77_mem)
  exact (rev172_plane57.combine rev172_plane77 2083356000000 2083356000000).xBoundCheck_sound rev172_s0_ll.nx rev172_s0_ll.dx true (by decide) p hc
theorem rev172_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev172_planes) : p.1≤rev172_s1_lr.real.1 := by
  have hc := rev172_plane1.combine_sound rev172_plane1 1 0 (by decide) (by decide) p
    (hp _ rev172_plane1_mem) (hp _ rev172_plane1_mem)
  exact (rev172_plane1.combine rev172_plane1 1 0).xBoundCheck_sound rev172_s1_lr.nx rev172_s1_lr.dx false (by decide) p hc
theorem rev172_hull (p : Point) (hp : p∈IntegerCarrier rev172_planes) :
    p∈rationalHull (fractionRow172.map FractionPoint.rational) := by
  have hxlo := rev172_bound0_lo p hp
  have hxhi := rev172_bound0_hi p hp
  by_cases h0 : p.1≤rev172_s0_lr.real.1
  · exact rev172_slab0 p hp hxlo h0
  exact rev172_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull172 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,4,14,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow172 := by
  rw [← fractionRow172_correct]
  exact rev172_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull172
