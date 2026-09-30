import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev37_planes : List IntegerPlane := integerOverlayPlanes ![3,1,15,8]
def rev37_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev37_plane2_mem : rev37_plane2 ∈ rev37_planes := by decide
def rev37_plane6 : IntegerPlane := ⟨(-1855520000000),287616000000,(-1356143759600)⟩
theorem rev37_plane6_mem : rev37_plane6 ∈ rev37_planes := by decide
def rev37_plane24 : IntegerPlane := ⟨2145688000000,699324000000,1695048727641⟩
theorem rev37_plane24_mem : rev37_plane24 ∈ rev37_planes := by decide
def rev37_plane55 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-1570721771568)⟩
theorem rev37_plane55_mem : rev37_plane55 ∈ rev37_planes := by decide
def rev37_vertex0 : FractionPoint := fractionRow37[0]!
theorem rev37_vertex0_mem : rev37_vertex0∈fractionRow37 := by decide
def rev37_vertex1 : FractionPoint := fractionRow37[1]!
theorem rev37_vertex1_mem : rev37_vertex1∈fractionRow37 := by decide
def rev37_vertex2 : FractionPoint := fractionRow37[2]!
theorem rev37_vertex2_mem : rev37_vertex2∈fractionRow37 := by decide
def rev37_vertex3 : FractionPoint := fractionRow37[3]!
theorem rev37_vertex3_mem : rev37_vertex3∈fractionRow37 := by decide
def rev37_s0_ll : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev37_s0_ll_mem : rev37_s0_ll.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane55 rev37_vertex3 rev37_vertex0 rev37_s0_ll
    rev37_vertex3_mem rev37_vertex0_mem (by decide)
def rev37_s0_lr : FractionPoint := ⟨32723370241,44576750000,0,1⟩
theorem rev37_s0_lr_mem : rev37_s0_lr.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane55 rev37_vertex3 rev37_vertex0 rev37_s0_lr
    rev37_vertex3_mem rev37_vertex0_mem (by decide)
def rev37_s0_ul : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev37_s0_ul_mem : rev37_s0_ul.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane6 rev37_vertex3 rev37_vertex2 rev37_s0_ul
    rev37_vertex3_mem rev37_vertex2_mem (by decide)
def rev37_s0_ur : FractionPoint := ⟨32723370241,44576750000,13319330691551,641049326400000⟩
theorem rev37_s0_ur_mem : rev37_s0_ur.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane6 rev37_vertex3 rev37_vertex2 rev37_s0_ur
    rev37_vertex3_mem rev37_vertex2_mem (by decide)
theorem rev37_slab0 (p : Point) (hp : p∈IntegerCarrier rev37_planes)
    (hx0 : rev37_s0_ll.real.1≤p.1) (hx1 : p.1≤rev37_s0_lr.real.1) :
    p∈rationalHull (fractionRow37.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev37_plane55 rev37_plane6 rev37_s0_ll rev37_s0_lr rev37_s0_ul rev37_s0_ur
    (by decide) rev37_s0_ll_mem rev37_s0_lr_mem rev37_s0_ul_mem rev37_s0_ur_mem p
    (hp _ rev37_plane55_mem) (hp _ rev37_plane6_mem) hx0 hx1
def rev37_s1_ll : FractionPoint := ⟨32723370241,44576750000,0,1⟩
theorem rev37_s1_ll_mem : rev37_s1_ll.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane2 rev37_vertex0 rev37_vertex1 rev37_s1_ll
    rev37_vertex0_mem rev37_vertex1_mem (by decide)
def rev37_s1_lr : FractionPoint := ⟨7478682361394293,9972624314000000,0,1⟩
theorem rev37_s1_lr_mem : rev37_s1_lr.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane2 rev37_vertex0 rev37_vertex1 rev37_s1_lr
    rev37_vertex0_mem rev37_vertex1_mem (by decide)
def rev37_s1_ul : FractionPoint := ⟨32723370241,44576750000,13319330691551,641049326400000⟩
theorem rev37_s1_ul_mem : rev37_s1_ul.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane6 rev37_vertex3 rev37_vertex2 rev37_s1_ul
    rev37_vertex3_mem rev37_vertex2_mem (by decide)
def rev37_s1_ur : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev37_s1_ur_mem : rev37_s1_ur.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane6 rev37_vertex3 rev37_vertex2 rev37_s1_ur
    rev37_vertex3_mem rev37_vertex2_mem (by decide)
theorem rev37_slab1 (p : Point) (hp : p∈IntegerCarrier rev37_planes)
    (hx0 : rev37_s1_ll.real.1≤p.1) (hx1 : p.1≤rev37_s1_lr.real.1) :
    p∈rationalHull (fractionRow37.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev37_plane2 rev37_plane6 rev37_s1_ll rev37_s1_lr rev37_s1_ul rev37_s1_ur
    (by decide) rev37_s1_ll_mem rev37_s1_lr_mem rev37_s1_ul_mem rev37_s1_ur_mem p
    (hp _ rev37_plane2_mem) (hp _ rev37_plane6_mem) hx0 hx1
def rev37_s2_ll : FractionPoint := ⟨7478682361394293,9972624314000000,0,1⟩
theorem rev37_s2_ll_mem : rev37_s2_ll.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane2 rev37_vertex0 rev37_vertex1 rev37_s2_ll
    rev37_vertex0_mem rev37_vertex1_mem (by decide)
def rev37_s2_lr : FractionPoint := ⟨1695048727641,2145688000000,0,1⟩
theorem rev37_s2_lr_mem : rev37_s2_lr.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane2 rev37_vertex0 rev37_vertex1 rev37_s2_lr
    rev37_vertex0_mem rev37_vertex1_mem (by decide)
def rev37_s2_ul : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev37_s2_ul_mem : rev37_s2_ul.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane24 rev37_vertex2 rev37_vertex1 rev37_s2_ul
    rev37_vertex2_mem rev37_vertex1_mem (by decide)
def rev37_s2_ur : FractionPoint := ⟨1695048727641,2145688000000,0,1⟩
theorem rev37_s2_ur_mem : rev37_s2_ur.real ∈ rationalHull (fractionRow37.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow37 rev37_plane24 rev37_vertex2 rev37_vertex1 rev37_s2_ur
    rev37_vertex2_mem rev37_vertex1_mem (by decide)
theorem rev37_slab2 (p : Point) (hp : p∈IntegerCarrier rev37_planes)
    (hx0 : rev37_s2_ll.real.1≤p.1) (hx1 : p.1≤rev37_s2_lr.real.1) :
    p∈rationalHull (fractionRow37.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev37_plane2 rev37_plane24 rev37_s2_ll rev37_s2_lr rev37_s2_ul rev37_s2_ur
    (by decide) rev37_s2_ll_mem rev37_s2_lr_mem rev37_s2_ul_mem rev37_s2_ur_mem p
    (hp _ rev37_plane2_mem) (hp _ rev37_plane24_mem) hx0 hx1
theorem rev37_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev37_planes) : rev37_s0_ll.real.1≤p.1 := by
  have hc := rev37_plane6.combine_sound rev37_plane55 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev37_plane6_mem) (hp _ rev37_plane55_mem)
  exact (rev37_plane6.combine rev37_plane55 15204000000 287616000000).xBoundCheck_sound rev37_s0_ll.nx rev37_s0_ll.dx true (by decide) p hc
theorem rev37_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev37_planes) : p.1≤rev37_s2_lr.real.1 := by
  have hc := rev37_plane2.combine_sound rev37_plane24 699324000000 1 (by decide) (by decide) p
    (hp _ rev37_plane2_mem) (hp _ rev37_plane24_mem)
  exact (rev37_plane2.combine rev37_plane24 699324000000 1).xBoundCheck_sound rev37_s2_lr.nx rev37_s2_lr.dx false (by decide) p hc
theorem rev37_hull (p : Point) (hp : p∈IntegerCarrier rev37_planes) :
    p∈rationalHull (fractionRow37.map FractionPoint.rational) := by
  have hxlo := rev37_bound0_lo p hp
  have hxhi := rev37_bound0_hi p hp
  by_cases h0 : p.1≤rev37_s0_lr.real.1
  · exact rev37_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev37_s1_lr.real.1
  · exact rev37_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev37_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull37 (p : Point)
    (hp : ∀ g, ClosedCell ((![3,1,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow37 := by
  rw [← fractionRow37_correct]
  exact rev37_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull37
