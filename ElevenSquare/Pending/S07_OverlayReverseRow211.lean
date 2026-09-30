import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev211_planes : List IntegerPlane := integerOverlayPlanes ![15,8,12,14]
def rev211_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev211_plane1_mem : rev211_plane1 ∈ rev211_planes := by decide
def rev211_plane15 : IntegerPlane := ⟨15204000000,(-2139684000000),(-1555517771568)⟩
theorem rev211_plane15_mem : rev211_plane15 ∈ rev211_planes := by decide
def rev211_plane57 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-1643759759600)⟩
theorem rev211_plane57_mem : rev211_plane57 ∈ rev211_planes := by decide
def rev211_plane79 : IntegerPlane := ⟨(-699324000000),2145688000000,995724727641⟩
theorem rev211_plane79_mem : rev211_plane79 ∈ rev211_planes := by decide
def rev211_vertex0 : FractionPoint := fractionRow211[0]!
theorem rev211_vertex0_mem : rev211_vertex0∈fractionRow211 := by decide
def rev211_vertex1 : FractionPoint := fractionRow211[1]!
theorem rev211_vertex1_mem : rev211_vertex1∈fractionRow211 := by decide
def rev211_vertex2 : FractionPoint := fractionRow211[2]!
theorem rev211_vertex2_mem : rev211_vertex2∈fractionRow211 := by decide
def rev211_vertex3 : FractionPoint := fractionRow211[3]!
theorem rev211_vertex3_mem : rev211_vertex3∈fractionRow211 := by decide
def rev211_s0_ll : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev211_s0_ll_mem : rev211_s0_ll.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane57 rev211_vertex2 rev211_vertex3 rev211_s0_ll
    rev211_vertex2_mem rev211_vertex3_mem (by decide)
def rev211_s0_lr : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev211_s0_lr_mem : rev211_s0_lr.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane57 rev211_vertex2 rev211_vertex3 rev211_s0_lr
    rev211_vertex2_mem rev211_vertex3_mem (by decide)
def rev211_s0_ul : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev211_s0_ul_mem : rev211_s0_ul.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane79 rev211_vertex2 rev211_vertex1 rev211_s0_ul
    rev211_vertex2_mem rev211_vertex1_mem (by decide)
def rev211_s0_ur : FractionPoint := ⟨657116793708449,670436124400000,2817768430030612457541,3596366867228968000000⟩
theorem rev211_s0_ur_mem : rev211_s0_ur.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane79 rev211_vertex2 rev211_vertex1 rev211_s0_ur
    rev211_vertex2_mem rev211_vertex1_mem (by decide)
theorem rev211_slab0 (p : Point) (hp : p∈IntegerCarrier rev211_planes)
    (hx0 : rev211_s0_ll.real.1≤p.1) (hx1 : p.1≤rev211_s0_lr.real.1) :
    p∈rationalHull (fractionRow211.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev211_plane57 rev211_plane79 rev211_s0_ll rev211_s0_lr rev211_s0_ul rev211_s0_ur
    (by decide) rev211_s0_ll_mem rev211_s0_lr_mem rev211_s0_ul_mem rev211_s0_ur_mem p
    (hp _ rev211_plane57_mem) (hp _ rev211_plane79_mem) hx0 hx1
def rev211_s1_ll : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev211_s1_ll_mem : rev211_s1_ll.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane15 rev211_vertex3 rev211_vertex0 rev211_s1_ll
    rev211_vertex3_mem rev211_vertex0_mem (by decide)
def rev211_s1_lr : FractionPoint := ⟨1,1,32723370241,44576750000⟩
theorem rev211_s1_lr_mem : rev211_s1_lr.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane15 rev211_vertex3 rev211_vertex0 rev211_s1_lr
    rev211_vertex3_mem rev211_vertex0_mem (by decide)
def rev211_s1_ul : FractionPoint := ⟨657116793708449,670436124400000,2817768430030612457541,3596366867228968000000⟩
theorem rev211_s1_ul_mem : rev211_s1_ul.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane79 rev211_vertex2 rev211_vertex1 rev211_s1_ul
    rev211_vertex2_mem rev211_vertex1_mem (by decide)
def rev211_s1_ur : FractionPoint := ⟨1,1,1695048727641,2145688000000⟩
theorem rev211_s1_ur_mem : rev211_s1_ur.real ∈ rationalHull (fractionRow211.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow211 rev211_plane79 rev211_vertex2 rev211_vertex1 rev211_s1_ur
    rev211_vertex2_mem rev211_vertex1_mem (by decide)
theorem rev211_slab1 (p : Point) (hp : p∈IntegerCarrier rev211_planes)
    (hx0 : rev211_s1_ll.real.1≤p.1) (hx1 : p.1≤rev211_s1_lr.real.1) :
    p∈rationalHull (fractionRow211.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev211_plane15 rev211_plane79 rev211_s1_ll rev211_s1_lr rev211_s1_ul rev211_s1_ur
    (by decide) rev211_s1_ll_mem rev211_s1_lr_mem rev211_s1_ul_mem rev211_s1_ur_mem p
    (hp _ rev211_plane15_mem) (hp _ rev211_plane79_mem) hx0 hx1
theorem rev211_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev211_planes) : rev211_s0_ll.real.1≤p.1 := by
  have hc := rev211_plane57.combine_sound rev211_plane79 2145688000000 1855520000000 (by decide) (by decide) p
    (hp _ rev211_plane57_mem) (hp _ rev211_plane79_mem)
  exact (rev211_plane57.combine rev211_plane79 2145688000000 1855520000000).xBoundCheck_sound rev211_s0_ll.nx rev211_s0_ll.dx true (by decide) p hc
theorem rev211_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev211_planes) : p.1≤rev211_s1_lr.real.1 := by
  have hc := rev211_plane1.combine_sound rev211_plane1 1 0 (by decide) (by decide) p
    (hp _ rev211_plane1_mem) (hp _ rev211_plane1_mem)
  exact (rev211_plane1.combine rev211_plane1 1 0).xBoundCheck_sound rev211_s1_lr.nx rev211_s1_lr.dx false (by decide) p hc
theorem rev211_hull (p : Point) (hp : p∈IntegerCarrier rev211_planes) :
    p∈rationalHull (fractionRow211.map FractionPoint.rational) := by
  have hxlo := rev211_bound0_lo p hp
  have hxhi := rev211_bound0_hi p hp
  by_cases h0 : p.1≤rev211_s0_lr.real.1
  · exact rev211_slab0 p hp hxlo h0
  exact rev211_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull211 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,12,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow211 := by
  rw [← fractionRow211_correct]
  exact rev211_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull211
