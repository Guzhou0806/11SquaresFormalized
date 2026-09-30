import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev18_planes : List IntegerPlane := integerOverlayPlanes ![1,3,7,0]
def rev18_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev18_plane2_mem : rev18_plane2 ∈ rev18_planes := by decide
def rev18_plane4 : IntegerPlane := ⟨(-2145688000000),699324000000,(-450639272359)⟩
theorem rev18_plane4_mem : rev18_plane4 ∈ rev18_planes := by decide
def rev18_plane26 : IntegerPlane := ⟨1855520000000,287616000000,499376240400⟩
theorem rev18_plane26_mem : rev18_plane26 ∈ rev18_planes := by decide
def rev18_plane68 : IntegerPlane := ⟨2139684000000,(-15204000000),568962228432⟩
theorem rev18_plane68_mem : rev18_plane68 ∈ rev18_planes := by decide
def rev18_vertex0 : FractionPoint := fractionRow18[0]!
theorem rev18_vertex0_mem : rev18_vertex0∈fractionRow18 := by decide
def rev18_vertex1 : FractionPoint := fractionRow18[1]!
theorem rev18_vertex1_mem : rev18_vertex1∈fractionRow18 := by decide
def rev18_vertex2 : FractionPoint := fractionRow18[2]!
theorem rev18_vertex2_mem : rev18_vertex2∈fractionRow18 := by decide
def rev18_vertex3 : FractionPoint := fractionRow18[3]!
theorem rev18_vertex3_mem : rev18_vertex3∈fractionRow18 := by decide
def rev18_s0_ll : FractionPoint := ⟨450639272359,2145688000000,0,1⟩
theorem rev18_s0_ll_mem : rev18_s0_ll.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane2 rev18_vertex0 rev18_vertex1 rev18_s0_ll
    rev18_vertex0_mem rev18_vertex1_mem (by decide)
def rev18_s0_lr : FractionPoint := ⟨2493941952605707,9972624314000000,0,1⟩
theorem rev18_s0_lr_mem : rev18_s0_lr.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane2 rev18_vertex0 rev18_vertex1 rev18_s0_lr
    rev18_vertex0_mem rev18_vertex1_mem (by decide)
def rev18_s0_ul : FractionPoint := ⟨450639272359,2145688000000,0,1⟩
theorem rev18_s0_ul_mem : rev18_s0_ul.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane4 rev18_vertex0 rev18_vertex3 rev18_s0_ul
    rev18_vertex0_mem rev18_vertex3_mem (by decide)
def rev18_s0_ur : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev18_s0_ur_mem : rev18_s0_ur.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane4 rev18_vertex0 rev18_vertex3 rev18_s0_ur
    rev18_vertex0_mem rev18_vertex3_mem (by decide)
theorem rev18_slab0 (p : Point) (hp : p∈IntegerCarrier rev18_planes)
    (hx0 : rev18_s0_ll.real.1≤p.1) (hx1 : p.1≤rev18_s0_lr.real.1) :
    p∈rationalHull (fractionRow18.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev18_plane2 rev18_plane4 rev18_s0_ll rev18_s0_lr rev18_s0_ul rev18_s0_ur
    (by decide) rev18_s0_ll_mem rev18_s0_lr_mem rev18_s0_ul_mem rev18_s0_ur_mem p
    (hp _ rev18_plane2_mem) (hp _ rev18_plane4_mem) hx0 hx1
def rev18_s1_ll : FractionPoint := ⟨2493941952605707,9972624314000000,0,1⟩
theorem rev18_s1_ll_mem : rev18_s1_ll.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane2 rev18_vertex0 rev18_vertex1 rev18_s1_ll
    rev18_vertex0_mem rev18_vertex1_mem (by decide)
def rev18_s1_lr : FractionPoint := ⟨11853379759,44576750000,0,1⟩
theorem rev18_s1_lr_mem : rev18_s1_lr.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane2 rev18_vertex0 rev18_vertex1 rev18_s1_lr
    rev18_vertex0_mem rev18_vertex1_mem (by decide)
def rev18_s1_ul : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev18_s1_ul_mem : rev18_s1_ul.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane26 rev18_vertex3 rev18_vertex2 rev18_s1_ul
    rev18_vertex3_mem rev18_vertex2_mem (by decide)
def rev18_s1_ur : FractionPoint := ⟨11853379759,44576750000,13319330691551,641049326400000⟩
theorem rev18_s1_ur_mem : rev18_s1_ur.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane26 rev18_vertex3 rev18_vertex2 rev18_s1_ur
    rev18_vertex3_mem rev18_vertex2_mem (by decide)
theorem rev18_slab1 (p : Point) (hp : p∈IntegerCarrier rev18_planes)
    (hx0 : rev18_s1_ll.real.1≤p.1) (hx1 : p.1≤rev18_s1_lr.real.1) :
    p∈rationalHull (fractionRow18.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev18_plane2 rev18_plane26 rev18_s1_ll rev18_s1_lr rev18_s1_ul rev18_s1_ur
    (by decide) rev18_s1_ll_mem rev18_s1_lr_mem rev18_s1_ul_mem rev18_s1_ur_mem p
    (hp _ rev18_plane2_mem) (hp _ rev18_plane26_mem) hx0 hx1
def rev18_s2_ll : FractionPoint := ⟨11853379759,44576750000,0,1⟩
theorem rev18_s2_ll_mem : rev18_s2_ll.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane68 rev18_vertex1 rev18_vertex2 rev18_s2_ll
    rev18_vertex1_mem rev18_vertex2_mem (by decide)
def rev18_s2_lr : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev18_s2_lr_mem : rev18_s2_lr.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane68 rev18_vertex1 rev18_vertex2 rev18_s2_lr
    rev18_vertex1_mem rev18_vertex2_mem (by decide)
def rev18_s2_ul : FractionPoint := ⟨11853379759,44576750000,13319330691551,641049326400000⟩
theorem rev18_s2_ul_mem : rev18_s2_ul.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane26 rev18_vertex3 rev18_vertex2 rev18_s2_ul
    rev18_vertex3_mem rev18_vertex2_mem (by decide)
def rev18_s2_ur : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev18_s2_ur_mem : rev18_s2_ur.real ∈ rationalHull (fractionRow18.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow18 rev18_plane26 rev18_vertex3 rev18_vertex2 rev18_s2_ur
    rev18_vertex3_mem rev18_vertex2_mem (by decide)
theorem rev18_slab2 (p : Point) (hp : p∈IntegerCarrier rev18_planes)
    (hx0 : rev18_s2_ll.real.1≤p.1) (hx1 : p.1≤rev18_s2_lr.real.1) :
    p∈rationalHull (fractionRow18.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev18_plane68 rev18_plane26 rev18_s2_ll rev18_s2_lr rev18_s2_ul rev18_s2_ur
    (by decide) rev18_s2_ll_mem rev18_s2_lr_mem rev18_s2_ul_mem rev18_s2_ur_mem p
    (hp _ rev18_plane68_mem) (hp _ rev18_plane26_mem) hx0 hx1
theorem rev18_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev18_planes) : rev18_s0_ll.real.1≤p.1 := by
  have hc := rev18_plane2.combine_sound rev18_plane4 699324000000 1 (by decide) (by decide) p
    (hp _ rev18_plane2_mem) (hp _ rev18_plane4_mem)
  exact (rev18_plane2.combine rev18_plane4 699324000000 1).xBoundCheck_sound rev18_s0_ll.nx rev18_s0_ll.dx true (by decide) p hc
theorem rev18_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev18_planes) : p.1≤rev18_s2_lr.real.1 := by
  have hc := rev18_plane26.combine_sound rev18_plane68 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev18_plane26_mem) (hp _ rev18_plane68_mem)
  exact (rev18_plane26.combine rev18_plane68 15204000000 287616000000).xBoundCheck_sound rev18_s2_lr.nx rev18_s2_lr.dx false (by decide) p hc
theorem rev18_hull (p : Point) (hp : p∈IntegerCarrier rev18_planes) :
    p∈rationalHull (fractionRow18.map FractionPoint.rational) := by
  have hxlo := rev18_bound0_lo p hp
  have hxhi := rev18_bound0_hi p hp
  by_cases h0 : p.1≤rev18_s0_lr.real.1
  · exact rev18_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev18_s1_lr.real.1
  · exact rev18_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev18_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull18 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,3,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow18 := by
  rw [← fractionRow18_correct]
  exact rev18_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull18
