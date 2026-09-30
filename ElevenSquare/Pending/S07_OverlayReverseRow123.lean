import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev123_planes : List IntegerPlane := integerOverlayPlanes ![8,15,1,3]
def rev123_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev123_plane0_mem : rev123_plane0 ∈ rev123_planes := by decide
def rev123_plane35 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-1570721771568)⟩
theorem rev123_plane35_mem : rev123_plane35 ∈ rev123_planes := by decide
def rev123_plane44 : IntegerPlane := ⟨699324000000,2145688000000,1695048727641⟩
theorem rev123_plane44_mem : rev123_plane44 ∈ rev123_planes := by decide
def rev123_plane66 : IntegerPlane := ⟨287616000000,(-1855520000000),(-1356143759600)⟩
theorem rev123_plane66_mem : rev123_plane66 ∈ rev123_planes := by decide
def rev123_vertex0 : FractionPoint := fractionRow123[0]!
theorem rev123_vertex0_mem : rev123_vertex0∈fractionRow123 := by decide
def rev123_vertex1 : FractionPoint := fractionRow123[1]!
theorem rev123_vertex1_mem : rev123_vertex1∈fractionRow123 := by decide
def rev123_vertex2 : FractionPoint := fractionRow123[2]!
theorem rev123_vertex2_mem : rev123_vertex2∈fractionRow123 := by decide
def rev123_vertex3 : FractionPoint := fractionRow123[3]!
theorem rev123_vertex3_mem : rev123_vertex3∈fractionRow123 := by decide
def rev123_s0_ll : FractionPoint := ⟨0,1,32723370241,44576750000⟩
theorem rev123_s0_ll_mem : rev123_s0_ll.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane35 rev123_vertex1 rev123_vertex2 rev123_s0_ll
    rev123_vertex1_mem rev123_vertex2_mem (by decide)
def rev123_s0_lr : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev123_s0_lr_mem : rev123_s0_lr.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane35 rev123_vertex1 rev123_vertex2 rev123_s0_lr
    rev123_vertex1_mem rev123_vertex2_mem (by decide)
def rev123_s0_ul : FractionPoint := ⟨0,1,1695048727641,2145688000000⟩
theorem rev123_s0_ul_mem : rev123_s0_ul.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane44 rev123_vertex0 rev123_vertex3 rev123_s0_ul
    rev123_vertex0_mem rev123_vertex3_mem (by decide)
def rev123_s0_ur : FractionPoint := ⟨13319330691551,670436124400000,2817768430030612457541,3596366867228968000000⟩
theorem rev123_s0_ur_mem : rev123_s0_ur.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane44 rev123_vertex0 rev123_vertex3 rev123_s0_ur
    rev123_vertex0_mem rev123_vertex3_mem (by decide)
theorem rev123_slab0 (p : Point) (hp : p∈IntegerCarrier rev123_planes)
    (hx0 : rev123_s0_ll.real.1≤p.1) (hx1 : p.1≤rev123_s0_lr.real.1) :
    p∈rationalHull (fractionRow123.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev123_plane35 rev123_plane44 rev123_s0_ll rev123_s0_lr rev123_s0_ul rev123_s0_ur
    (by decide) rev123_s0_ll_mem rev123_s0_lr_mem rev123_s0_ul_mem rev123_s0_ur_mem p
    (hp _ rev123_plane35_mem) (hp _ rev123_plane44_mem) hx0 hx1
def rev123_s1_ll : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev123_s1_ll_mem : rev123_s1_ll.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane66 rev123_vertex2 rev123_vertex3 rev123_s1_ll
    rev123_vertex2_mem rev123_vertex3_mem (by decide)
def rev123_s1_lr : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev123_s1_lr_mem : rev123_s1_lr.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane66 rev123_vertex2 rev123_vertex3 rev123_s1_lr
    rev123_vertex2_mem rev123_vertex3_mem (by decide)
def rev123_s1_ul : FractionPoint := ⟨13319330691551,670436124400000,2817768430030612457541,3596366867228968000000⟩
theorem rev123_s1_ul_mem : rev123_s1_ul.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane44 rev123_vertex0 rev123_vertex3 rev123_s1_ul
    rev123_vertex0_mem rev123_vertex3_mem (by decide)
def rev123_s1_ur : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev123_s1_ur_mem : rev123_s1_ur.real ∈ rationalHull (fractionRow123.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow123 rev123_plane44 rev123_vertex0 rev123_vertex3 rev123_s1_ur
    rev123_vertex0_mem rev123_vertex3_mem (by decide)
theorem rev123_slab1 (p : Point) (hp : p∈IntegerCarrier rev123_planes)
    (hx0 : rev123_s1_ll.real.1≤p.1) (hx1 : p.1≤rev123_s1_lr.real.1) :
    p∈rationalHull (fractionRow123.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev123_plane66 rev123_plane44 rev123_s1_ll rev123_s1_lr rev123_s1_ul rev123_s1_ur
    (by decide) rev123_s1_ll_mem rev123_s1_lr_mem rev123_s1_ul_mem rev123_s1_ur_mem p
    (hp _ rev123_plane66_mem) (hp _ rev123_plane44_mem) hx0 hx1
theorem rev123_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev123_planes) : rev123_s0_ll.real.1≤p.1 := by
  have hc := rev123_plane0.combine_sound rev123_plane0 1 0 (by decide) (by decide) p
    (hp _ rev123_plane0_mem) (hp _ rev123_plane0_mem)
  exact (rev123_plane0.combine rev123_plane0 1 0).xBoundCheck_sound rev123_s0_ll.nx rev123_s0_ll.dx true (by decide) p hc
theorem rev123_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev123_planes) : p.1≤rev123_s1_lr.real.1 := by
  have hc := rev123_plane44.combine_sound rev123_plane66 1855520000000 2145688000000 (by decide) (by decide) p
    (hp _ rev123_plane44_mem) (hp _ rev123_plane66_mem)
  exact (rev123_plane44.combine rev123_plane66 1855520000000 2145688000000).xBoundCheck_sound rev123_s1_lr.nx rev123_s1_lr.dx false (by decide) p hc
theorem rev123_hull (p : Point) (hp : p∈IntegerCarrier rev123_planes) :
    p∈rationalHull (fractionRow123.map FractionPoint.rational) := by
  have hxlo := rev123_bound0_lo p hp
  have hxhi := rev123_bound0_hi p hp
  by_cases h0 : p.1≤rev123_s0_lr.real.1
  · exact rev123_slab0 p hp hxlo h0
  exact rev123_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull123 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,1,3] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow123 := by
  rw [← fractionRow123_correct]
  exact rev123_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull123
