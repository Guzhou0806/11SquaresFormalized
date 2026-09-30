import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev19_planes : List IntegerPlane := integerOverlayPlanes ![1,3,7,4]
def rev19_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev19_plane2_mem : rev19_plane2 ∈ rev19_planes := by decide
def rev19_plane26 : IntegerPlane := ⟨1855520000000,287616000000,499376240400⟩
theorem rev19_plane26_mem : rev19_plane26 ∈ rev19_planes := by decide
def rev19_plane64 : IntegerPlane := ⟨(-2139684000000),15204000000,(-568962228432)⟩
theorem rev19_plane64_mem : rev19_plane64 ∈ rev19_planes := by decide
def rev19_vertex0 : FractionPoint := fractionRow19[0]!
theorem rev19_vertex0_mem : rev19_vertex0∈fractionRow19 := by decide
def rev19_vertex1 : FractionPoint := fractionRow19[1]!
theorem rev19_vertex1_mem : rev19_vertex1∈fractionRow19 := by decide
def rev19_vertex2 : FractionPoint := fractionRow19[2]!
theorem rev19_vertex2_mem : rev19_vertex2∈fractionRow19 := by decide
def rev19_s0_ll : FractionPoint := ⟨11853379759,44576750000,0,1⟩
theorem rev19_s0_ll_mem : rev19_s0_ll.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane2 rev19_vertex0 rev19_vertex1 rev19_s0_ll
    rev19_vertex0_mem rev19_vertex1_mem (by decide)
def rev19_s0_lr : FractionPoint := ⟨127407110603973,478882946000000,0,1⟩
theorem rev19_s0_lr_mem : rev19_s0_lr.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane2 rev19_vertex0 rev19_vertex1 rev19_s0_lr
    rev19_vertex0_mem rev19_vertex1_mem (by decide)
def rev19_s0_ul : FractionPoint := ⟨11853379759,44576750000,0,1⟩
theorem rev19_s0_ul_mem : rev19_s0_ul.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane64 rev19_vertex0 rev19_vertex2 rev19_s0_ul
    rev19_vertex0_mem rev19_vertex2_mem (by decide)
def rev19_s0_ur : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev19_s0_ur_mem : rev19_s0_ur.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane64 rev19_vertex0 rev19_vertex2 rev19_s0_ur
    rev19_vertex0_mem rev19_vertex2_mem (by decide)
theorem rev19_slab0 (p : Point) (hp : p∈IntegerCarrier rev19_planes)
    (hx0 : rev19_s0_ll.real.1≤p.1) (hx1 : p.1≤rev19_s0_lr.real.1) :
    p∈rationalHull (fractionRow19.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev19_plane2 rev19_plane64 rev19_s0_ll rev19_s0_lr rev19_s0_ul rev19_s0_ur
    (by decide) rev19_s0_ll_mem rev19_s0_lr_mem rev19_s0_ul_mem rev19_s0_ur_mem p
    (hp _ rev19_plane2_mem) (hp _ rev19_plane64_mem) hx0 hx1
def rev19_s1_ll : FractionPoint := ⟨127407110603973,478882946000000,0,1⟩
theorem rev19_s1_ll_mem : rev19_s1_ll.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane2 rev19_vertex0 rev19_vertex1 rev19_s1_ll
    rev19_vertex0_mem rev19_vertex1_mem (by decide)
def rev19_s1_lr : FractionPoint := ⟨1248440601,4638800000,0,1⟩
theorem rev19_s1_lr_mem : rev19_s1_lr.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane2 rev19_vertex0 rev19_vertex1 rev19_s1_lr
    rev19_vertex0_mem rev19_vertex1_mem (by decide)
def rev19_s1_ul : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev19_s1_ul_mem : rev19_s1_ul.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane26 rev19_vertex2 rev19_vertex1 rev19_s1_ul
    rev19_vertex2_mem rev19_vertex1_mem (by decide)
def rev19_s1_ur : FractionPoint := ⟨1248440601,4638800000,0,1⟩
theorem rev19_s1_ur_mem : rev19_s1_ur.real ∈ rationalHull (fractionRow19.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow19 rev19_plane26 rev19_vertex2 rev19_vertex1 rev19_s1_ur
    rev19_vertex2_mem rev19_vertex1_mem (by decide)
theorem rev19_slab1 (p : Point) (hp : p∈IntegerCarrier rev19_planes)
    (hx0 : rev19_s1_ll.real.1≤p.1) (hx1 : p.1≤rev19_s1_lr.real.1) :
    p∈rationalHull (fractionRow19.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev19_plane2 rev19_plane26 rev19_s1_ll rev19_s1_lr rev19_s1_ul rev19_s1_ur
    (by decide) rev19_s1_ll_mem rev19_s1_lr_mem rev19_s1_ul_mem rev19_s1_ur_mem p
    (hp _ rev19_plane2_mem) (hp _ rev19_plane26_mem) hx0 hx1
theorem rev19_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev19_planes) : rev19_s0_ll.real.1≤p.1 := by
  have hc := rev19_plane2.combine_sound rev19_plane64 15204000000 1 (by decide) (by decide) p
    (hp _ rev19_plane2_mem) (hp _ rev19_plane64_mem)
  exact (rev19_plane2.combine rev19_plane64 15204000000 1).xBoundCheck_sound rev19_s0_ll.nx rev19_s0_ll.dx true (by decide) p hc
theorem rev19_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev19_planes) : p.1≤rev19_s1_lr.real.1 := by
  have hc := rev19_plane2.combine_sound rev19_plane26 287616000000 1 (by decide) (by decide) p
    (hp _ rev19_plane2_mem) (hp _ rev19_plane26_mem)
  exact (rev19_plane2.combine rev19_plane26 287616000000 1).xBoundCheck_sound rev19_s1_lr.nx rev19_s1_lr.dx false (by decide) p hc
theorem rev19_hull (p : Point) (hp : p∈IntegerCarrier rev19_planes) :
    p∈rationalHull (fractionRow19.map FractionPoint.rational) := by
  have hxlo := rev19_bound0_lo p hp
  have hxhi := rev19_bound0_hi p hp
  by_cases h0 : p.1≤rev19_s0_lr.real.1
  · exact rev19_slab0 p hp hxlo h0
  exact rev19_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull19 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,3,7,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow19 := by
  rw [← fractionRow19_correct]
  exact rev19_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull19
