import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev201_planes : List IntegerPlane := integerOverlayPlanes ![14,12,8,15]
def rev201_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev201_plane3_mem : rev201_plane3 ∈ rev201_planes := by decide
def rev201_plane19 : IntegerPlane := ⟨2145688000000,(-699324000000),995724727641⟩
theorem rev201_plane19_mem : rev201_plane19 ∈ rev201_planes := by decide
def rev201_plane37 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-1643759759600)⟩
theorem rev201_plane37_mem : rev201_plane37 ∈ rev201_planes := by decide
def rev201_plane75 : IntegerPlane := ⟨(-2139684000000),15204000000,(-1555517771568)⟩
theorem rev201_plane75_mem : rev201_plane75 ∈ rev201_planes := by decide
def rev201_vertex0 : FractionPoint := fractionRow201[0]!
theorem rev201_vertex0_mem : rev201_vertex0∈fractionRow201 := by decide
def rev201_vertex1 : FractionPoint := fractionRow201[1]!
theorem rev201_vertex1_mem : rev201_vertex1∈fractionRow201 := by decide
def rev201_vertex2 : FractionPoint := fractionRow201[2]!
theorem rev201_vertex2_mem : rev201_vertex2∈fractionRow201 := by decide
def rev201_vertex3 : FractionPoint := fractionRow201[3]!
theorem rev201_vertex3_mem : rev201_vertex3∈fractionRow201 := by decide
def rev201_s0_ll : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev201_s0_ll_mem : rev201_s0_ll.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane37 rev201_vertex2 rev201_vertex3 rev201_s0_ll
    rev201_vertex2_mem rev201_vertex3_mem (by decide)
def rev201_s0_lr : FractionPoint := ⟨32723370241,44576750000,627729995708449,641049326400000⟩
theorem rev201_s0_lr_mem : rev201_s0_lr.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane37 rev201_vertex2 rev201_vertex3 rev201_s0_lr
    rev201_vertex2_mem rev201_vertex3_mem (by decide)
def rev201_s0_ul : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev201_s0_ul_mem : rev201_s0_ul.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane75 rev201_vertex2 rev201_vertex1 rev201_s0_ul
    rev201_vertex2_mem rev201_vertex1_mem (by decide)
def rev201_s0_ur : FractionPoint := ⟨32723370241,44576750000,1,1⟩
theorem rev201_s0_ur_mem : rev201_s0_ur.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane75 rev201_vertex2 rev201_vertex1 rev201_s0_ur
    rev201_vertex2_mem rev201_vertex1_mem (by decide)
theorem rev201_slab0 (p : Point) (hp : p∈IntegerCarrier rev201_planes)
    (hx0 : rev201_s0_ll.real.1≤p.1) (hx1 : p.1≤rev201_s0_lr.real.1) :
    p∈rationalHull (fractionRow201.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev201_plane37 rev201_plane75 rev201_s0_ll rev201_s0_lr rev201_s0_ul rev201_s0_ur
    (by decide) rev201_s0_ll_mem rev201_s0_lr_mem rev201_s0_ul_mem rev201_s0_ur_mem p
    (hp _ rev201_plane37_mem) (hp _ rev201_plane75_mem) hx0 hx1
def rev201_s1_ll : FractionPoint := ⟨32723370241,44576750000,627729995708449,641049326400000⟩
theorem rev201_s1_ll_mem : rev201_s1_ll.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane37 rev201_vertex2 rev201_vertex3 rev201_s1_ll
    rev201_vertex2_mem rev201_vertex3_mem (by decide)
def rev201_s1_lr : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev201_s1_lr_mem : rev201_s1_lr.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane37 rev201_vertex2 rev201_vertex3 rev201_s1_lr
    rev201_vertex2_mem rev201_vertex3_mem (by decide)
def rev201_s1_ul : FractionPoint := ⟨32723370241,44576750000,1,1⟩
theorem rev201_s1_ul_mem : rev201_s1_ul.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane3 rev201_vertex1 rev201_vertex0 rev201_s1_ul
    rev201_vertex1_mem rev201_vertex0_mem (by decide)
def rev201_s1_ur : FractionPoint := ⟨7478682361394293,9972624314000000,1,1⟩
theorem rev201_s1_ur_mem : rev201_s1_ur.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane3 rev201_vertex1 rev201_vertex0 rev201_s1_ur
    rev201_vertex1_mem rev201_vertex0_mem (by decide)
theorem rev201_slab1 (p : Point) (hp : p∈IntegerCarrier rev201_planes)
    (hx0 : rev201_s1_ll.real.1≤p.1) (hx1 : p.1≤rev201_s1_lr.real.1) :
    p∈rationalHull (fractionRow201.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev201_plane37 rev201_plane3 rev201_s1_ll rev201_s1_lr rev201_s1_ul rev201_s1_ur
    (by decide) rev201_s1_ll_mem rev201_s1_lr_mem rev201_s1_ul_mem rev201_s1_ur_mem p
    (hp _ rev201_plane37_mem) (hp _ rev201_plane3_mem) hx0 hx1
def rev201_s2_ll : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev201_s2_ll_mem : rev201_s2_ll.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane19 rev201_vertex3 rev201_vertex0 rev201_s2_ll
    rev201_vertex3_mem rev201_vertex0_mem (by decide)
def rev201_s2_lr : FractionPoint := ⟨1695048727641,2145688000000,1,1⟩
theorem rev201_s2_lr_mem : rev201_s2_lr.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane19 rev201_vertex3 rev201_vertex0 rev201_s2_lr
    rev201_vertex3_mem rev201_vertex0_mem (by decide)
def rev201_s2_ul : FractionPoint := ⟨7478682361394293,9972624314000000,1,1⟩
theorem rev201_s2_ul_mem : rev201_s2_ul.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane3 rev201_vertex1 rev201_vertex0 rev201_s2_ul
    rev201_vertex1_mem rev201_vertex0_mem (by decide)
def rev201_s2_ur : FractionPoint := ⟨1695048727641,2145688000000,1,1⟩
theorem rev201_s2_ur_mem : rev201_s2_ur.real ∈ rationalHull (fractionRow201.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow201 rev201_plane3 rev201_vertex1 rev201_vertex0 rev201_s2_ur
    rev201_vertex1_mem rev201_vertex0_mem (by decide)
theorem rev201_slab2 (p : Point) (hp : p∈IntegerCarrier rev201_planes)
    (hx0 : rev201_s2_ll.real.1≤p.1) (hx1 : p.1≤rev201_s2_lr.real.1) :
    p∈rationalHull (fractionRow201.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev201_plane19 rev201_plane3 rev201_s2_ll rev201_s2_lr rev201_s2_ul rev201_s2_ur
    (by decide) rev201_s2_ll_mem rev201_s2_lr_mem rev201_s2_ul_mem rev201_s2_ur_mem p
    (hp _ rev201_plane19_mem) (hp _ rev201_plane3_mem) hx0 hx1
theorem rev201_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev201_planes) : rev201_s0_ll.real.1≤p.1 := by
  have hc := rev201_plane37.combine_sound rev201_plane75 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev201_plane37_mem) (hp _ rev201_plane75_mem)
  exact (rev201_plane37.combine rev201_plane75 15204000000 287616000000).xBoundCheck_sound rev201_s0_ll.nx rev201_s0_ll.dx true (by decide) p hc
theorem rev201_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev201_planes) : p.1≤rev201_s2_lr.real.1 := by
  have hc := rev201_plane3.combine_sound rev201_plane19 699324000000 1 (by decide) (by decide) p
    (hp _ rev201_plane3_mem) (hp _ rev201_plane19_mem)
  exact (rev201_plane3.combine rev201_plane19 699324000000 1).xBoundCheck_sound rev201_s2_lr.nx rev201_s2_lr.dx false (by decide) p hc
theorem rev201_hull (p : Point) (hp : p∈IntegerCarrier rev201_planes) :
    p∈rationalHull (fractionRow201.map FractionPoint.rational) := by
  have hxlo := rev201_bound0_lo p hp
  have hxhi := rev201_bound0_hi p hp
  by_cases h0 : p.1≤rev201_s0_lr.real.1
  · exact rev201_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev201_s1_lr.real.1
  · exact rev201_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev201_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull201 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,12,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow201 := by
  rw [← fractionRow201_correct]
  exact rev201_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull201
