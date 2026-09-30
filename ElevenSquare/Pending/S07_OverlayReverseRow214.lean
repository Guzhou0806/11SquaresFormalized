import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev214_planes : List IntegerPlane := integerOverlayPlanes ![15,8,13,14]
def rev214_plane15 : IntegerPlane := ⟨15204000000,(-2139684000000),(-1555517771568)⟩
theorem rev214_plane15_mem : rev214_plane15 ∈ rev214_planes := by decide
def rev214_plane56 : IntegerPlane := ⟨287616000000,1855520000000,1643759759600⟩
theorem rev214_plane56_mem : rev214_plane56 ∈ rev214_planes := by decide
def rev214_plane79 : IntegerPlane := ⟨(-699324000000),2145688000000,995724727641⟩
theorem rev214_plane79_mem : rev214_plane79 ∈ rev214_planes := by decide
def rev214_vertex0 : FractionPoint := fractionRow214[0]!
theorem rev214_vertex0_mem : rev214_vertex0∈fractionRow214 := by decide
def rev214_vertex1 : FractionPoint := fractionRow214[1]!
theorem rev214_vertex1_mem : rev214_vertex1∈fractionRow214 := by decide
def rev214_vertex2 : FractionPoint := fractionRow214[2]!
theorem rev214_vertex2_mem : rev214_vertex2∈fractionRow214 := by decide
def rev214_s0_ll : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev214_s0_ll_mem : rev214_s0_ll.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane15 rev214_vertex0 rev214_vertex1 rev214_s0_ll
    rev214_vertex0_mem rev214_vertex1_mem (by decide)
def rev214_s0_lr : FractionPoint := ⟨10496302777651103,11967149176800000,7822791252895487089681,10669132341338388000000⟩
theorem rev214_s0_lr_mem : rev214_s0_lr.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane15 rev214_vertex0 rev214_vertex1 rev214_s0_lr
    rev214_vertex0_mem rev214_vertex1_mem (by decide)
def rev214_s0_ul : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev214_s0_ul_mem : rev214_s0_ul.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane79 rev214_vertex0 rev214_vertex2 rev214_s0_ul
    rev214_vertex0_mem rev214_vertex2_mem (by decide)
def rev214_s0_ur : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev214_s0_ur_mem : rev214_s0_ur.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane79 rev214_vertex0 rev214_vertex2 rev214_s0_ur
    rev214_vertex0_mem rev214_vertex2_mem (by decide)
theorem rev214_slab0 (p : Point) (hp : p∈IntegerCarrier rev214_planes)
    (hx0 : rev214_s0_ll.real.1≤p.1) (hx1 : p.1≤rev214_s0_lr.real.1) :
    p∈rationalHull (fractionRow214.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev214_plane15 rev214_plane79 rev214_s0_ll rev214_s0_lr rev214_s0_ul rev214_s0_ur
    (by decide) rev214_s0_ll_mem rev214_s0_lr_mem rev214_s0_ul_mem rev214_s0_ur_mem p
    (hp _ rev214_plane15_mem) (hp _ rev214_plane79_mem) hx0 hx1
def rev214_s1_ll : FractionPoint := ⟨10496302777651103,11967149176800000,7822791252895487089681,10669132341338388000000⟩
theorem rev214_s1_ll_mem : rev214_s1_ll.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane15 rev214_vertex0 rev214_vertex1 rev214_s1_ll
    rev214_vertex0_mem rev214_vertex1_mem (by decide)
def rev214_s1_lr : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev214_s1_lr_mem : rev214_s1_lr.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane15 rev214_vertex0 rev214_vertex1 rev214_s1_lr
    rev214_vertex0_mem rev214_vertex1_mem (by decide)
def rev214_s1_ul : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev214_s1_ul_mem : rev214_s1_ul.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane56 rev214_vertex2 rev214_vertex1 rev214_s1_ul
    rev214_vertex2_mem rev214_vertex1_mem (by decide)
def rev214_s1_ur : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev214_s1_ur_mem : rev214_s1_ur.real ∈ rationalHull (fractionRow214.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow214 rev214_plane56 rev214_vertex2 rev214_vertex1 rev214_s1_ur
    rev214_vertex2_mem rev214_vertex1_mem (by decide)
theorem rev214_slab1 (p : Point) (hp : p∈IntegerCarrier rev214_planes)
    (hx0 : rev214_s1_ll.real.1≤p.1) (hx1 : p.1≤rev214_s1_lr.real.1) :
    p∈rationalHull (fractionRow214.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev214_plane15 rev214_plane56 rev214_s1_ll rev214_s1_lr rev214_s1_ul rev214_s1_ur
    (by decide) rev214_s1_ll_mem rev214_s1_lr_mem rev214_s1_ul_mem rev214_s1_ur_mem p
    (hp _ rev214_plane15_mem) (hp _ rev214_plane56_mem) hx0 hx1
theorem rev214_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev214_planes) : rev214_s0_ll.real.1≤p.1 := by
  have hc := rev214_plane15.combine_sound rev214_plane79 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev214_plane15_mem) (hp _ rev214_plane79_mem)
  exact (rev214_plane15.combine rev214_plane79 2145688000000 2139684000000).xBoundCheck_sound rev214_s0_ll.nx rev214_s0_ll.dx true (by decide) p hc
theorem rev214_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev214_planes) : p.1≤rev214_s1_lr.real.1 := by
  have hc := rev214_plane15.combine_sound rev214_plane56 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev214_plane15_mem) (hp _ rev214_plane56_mem)
  exact (rev214_plane15.combine rev214_plane56 1855520000000 2139684000000).xBoundCheck_sound rev214_s1_lr.nx rev214_s1_lr.dx false (by decide) p hc
theorem rev214_hull (p : Point) (hp : p∈IntegerCarrier rev214_planes) :
    p∈rationalHull (fractionRow214.map FractionPoint.rational) := by
  have hxlo := rev214_bound0_lo p hp
  have hxhi := rev214_bound0_hi p hp
  by_cases h0 : p.1≤rev214_s0_lr.real.1
  · exact rev214_slab0 p hp hxlo h0
  exact rev214_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull214 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,13,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow214 := by
  rw [← fractionRow214_correct]
  exact rev214_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull214
