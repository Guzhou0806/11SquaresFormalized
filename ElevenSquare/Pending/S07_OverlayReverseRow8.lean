import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev8_planes : List IntegerPlane := integerOverlayPlanes ![0,7,3,1]
def rev8_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev8_plane0_mem : rev8_plane0 ∈ rev8_planes := by decide
def rev8_plane8 : IntegerPlane := ⟨(-15204000000),2139684000000,568962228432⟩
theorem rev8_plane8_mem : rev8_plane8 ∈ rev8_planes := by decide
def rev8_plane46 : IntegerPlane := ⟨287616000000,1855520000000,499376240400⟩
theorem rev8_plane46_mem : rev8_plane46 ∈ rev8_planes := by decide
def rev8_plane64 : IntegerPlane := ⟨699324000000,(-2145688000000),(-450639272359)⟩
theorem rev8_plane64_mem : rev8_plane64 ∈ rev8_planes := by decide
def rev8_vertex0 : FractionPoint := fractionRow8[0]!
theorem rev8_vertex0_mem : rev8_vertex0∈fractionRow8 := by decide
def rev8_vertex1 : FractionPoint := fractionRow8[1]!
theorem rev8_vertex1_mem : rev8_vertex1∈fractionRow8 := by decide
def rev8_vertex2 : FractionPoint := fractionRow8[2]!
theorem rev8_vertex2_mem : rev8_vertex2∈fractionRow8 := by decide
def rev8_vertex3 : FractionPoint := fractionRow8[3]!
theorem rev8_vertex3_mem : rev8_vertex3∈fractionRow8 := by decide
def rev8_s0_ll : FractionPoint := ⟨0,1,450639272359,2145688000000⟩
theorem rev8_s0_ll_mem : rev8_s0_ll.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane64 rev8_vertex3 rev8_vertex0 rev8_s0_ll
    rev8_vertex3_mem rev8_vertex0_mem (by decide)
def rev8_s0_lr : FractionPoint := ⟨13319330691551,670436124400000,778598437198355542459,3596366867228968000000⟩
theorem rev8_s0_lr_mem : rev8_s0_lr.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane64 rev8_vertex3 rev8_vertex0 rev8_s0_lr
    rev8_vertex3_mem rev8_vertex0_mem (by decide)
def rev8_s0_ul : FractionPoint := ⟨0,1,11853379759,44576750000⟩
theorem rev8_s0_ul_mem : rev8_s0_ul.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane8 rev8_vertex2 rev8_vertex1 rev8_s0_ul
    rev8_vertex2_mem rev8_vertex1_mem (by decide)
def rev8_s0_ur : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev8_s0_ur_mem : rev8_s0_ur.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane8 rev8_vertex2 rev8_vertex1 rev8_s0_ur
    rev8_vertex2_mem rev8_vertex1_mem (by decide)
theorem rev8_slab0 (p : Point) (hp : p∈IntegerCarrier rev8_planes)
    (hx0 : rev8_s0_ll.real.1≤p.1) (hx1 : p.1≤rev8_s0_lr.real.1) :
    p∈rationalHull (fractionRow8.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev8_plane64 rev8_plane8 rev8_s0_ll rev8_s0_lr rev8_s0_ul rev8_s0_ur
    (by decide) rev8_s0_ll_mem rev8_s0_lr_mem rev8_s0_ul_mem rev8_s0_ur_mem p
    (hp _ rev8_plane64_mem) (hp _ rev8_plane8_mem) hx0 hx1
def rev8_s1_ll : FractionPoint := ⟨13319330691551,670436124400000,778598437198355542459,3596366867228968000000⟩
theorem rev8_s1_ll_mem : rev8_s1_ll.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane64 rev8_vertex3 rev8_vertex0 rev8_s1_ll
    rev8_vertex3_mem rev8_vertex0_mem (by decide)
def rev8_s1_lr : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev8_s1_lr_mem : rev8_s1_lr.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane64 rev8_vertex3 rev8_vertex0 rev8_s1_lr
    rev8_vertex3_mem rev8_vertex0_mem (by decide)
def rev8_s1_ul : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev8_s1_ul_mem : rev8_s1_ul.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane46 rev8_vertex1 rev8_vertex0 rev8_s1_ul
    rev8_vertex1_mem rev8_vertex0_mem (by decide)
def rev8_s1_ur : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev8_s1_ur_mem : rev8_s1_ur.real ∈ rationalHull (fractionRow8.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow8 rev8_plane46 rev8_vertex1 rev8_vertex0 rev8_s1_ur
    rev8_vertex1_mem rev8_vertex0_mem (by decide)
theorem rev8_slab1 (p : Point) (hp : p∈IntegerCarrier rev8_planes)
    (hx0 : rev8_s1_ll.real.1≤p.1) (hx1 : p.1≤rev8_s1_lr.real.1) :
    p∈rationalHull (fractionRow8.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev8_plane64 rev8_plane46 rev8_s1_ll rev8_s1_lr rev8_s1_ul rev8_s1_ur
    (by decide) rev8_s1_ll_mem rev8_s1_lr_mem rev8_s1_ul_mem rev8_s1_ur_mem p
    (hp _ rev8_plane64_mem) (hp _ rev8_plane46_mem) hx0 hx1
theorem rev8_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev8_planes) : rev8_s0_ll.real.1≤p.1 := by
  have hc := rev8_plane0.combine_sound rev8_plane0 1 0 (by decide) (by decide) p
    (hp _ rev8_plane0_mem) (hp _ rev8_plane0_mem)
  exact (rev8_plane0.combine rev8_plane0 1 0).xBoundCheck_sound rev8_s0_ll.nx rev8_s0_ll.dx true (by decide) p hc
theorem rev8_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev8_planes) : p.1≤rev8_s1_lr.real.1 := by
  have hc := rev8_plane46.combine_sound rev8_plane64 2145688000000 1855520000000 (by decide) (by decide) p
    (hp _ rev8_plane46_mem) (hp _ rev8_plane64_mem)
  exact (rev8_plane46.combine rev8_plane64 2145688000000 1855520000000).xBoundCheck_sound rev8_s1_lr.nx rev8_s1_lr.dx false (by decide) p hc
theorem rev8_hull (p : Point) (hp : p∈IntegerCarrier rev8_planes) :
    p∈rationalHull (fractionRow8.map FractionPoint.rational) := by
  have hxlo := rev8_bound0_lo p hp
  have hxhi := rev8_bound0_hi p hp
  by_cases h0 : p.1≤rev8_s0_lr.real.1
  · exact rev8_slab0 p hp hxlo h0
  exact rev8_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull8 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,3,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow8 := by
  rw [← fractionRow8_correct]
  exact rev8_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull8
