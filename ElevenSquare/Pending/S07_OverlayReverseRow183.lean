import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks22
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev183_planes : List IntegerPlane := integerOverlayPlanes ![12,14,4,7]
def rev183_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev183_plane3_mem : rev183_plane3 ∈ rev183_planes := by decide
def rev183_plane17 : IntegerPlane := ⟨1855520000000,(-287616000000),211760240400⟩
theorem rev183_plane17_mem : rev183_plane17 ∈ rev183_planes := by decide
def rev183_plane44 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-584166228432)⟩
theorem rev183_plane44_mem : rev183_plane44 ∈ rev183_planes := by decide
def rev183_vertex0 : FractionPoint := fractionRow183[0]!
theorem rev183_vertex0_mem : rev183_vertex0∈fractionRow183 := by decide
def rev183_vertex1 : FractionPoint := fractionRow183[1]!
theorem rev183_vertex1_mem : rev183_vertex1∈fractionRow183 := by decide
def rev183_vertex2 : FractionPoint := fractionRow183[2]!
theorem rev183_vertex2_mem : rev183_vertex2∈fractionRow183 := by decide
def rev183_s0_ll : FractionPoint := ⟨11853379759,44576750000,1,1⟩
theorem rev183_s0_ll_mem : rev183_s0_ll.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane44 rev183_vertex1 rev183_vertex2 rev183_s0_ll
    rev183_vertex1_mem rev183_vertex2_mem (by decide)
def rev183_s0_lr : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev183_s0_lr_mem : rev183_s0_lr.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane44 rev183_vertex1 rev183_vertex2 rev183_s0_lr
    rev183_vertex1_mem rev183_vertex2_mem (by decide)
def rev183_s0_ul : FractionPoint := ⟨11853379759,44576750000,1,1⟩
theorem rev183_s0_ul_mem : rev183_s0_ul.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane3 rev183_vertex1 rev183_vertex0 rev183_s0_ul
    rev183_vertex1_mem rev183_vertex0_mem (by decide)
def rev183_s0_ur : FractionPoint := ⟨127407110603973,478882946000000,1,1⟩
theorem rev183_s0_ur_mem : rev183_s0_ur.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane3 rev183_vertex1 rev183_vertex0 rev183_s0_ur
    rev183_vertex1_mem rev183_vertex0_mem (by decide)
theorem rev183_slab0 (p : Point) (hp : p∈IntegerCarrier rev183_planes)
    (hx0 : rev183_s0_ll.real.1≤p.1) (hx1 : p.1≤rev183_s0_lr.real.1) :
    p∈rationalHull (fractionRow183.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev183_plane44 rev183_plane3 rev183_s0_ll rev183_s0_lr rev183_s0_ul rev183_s0_ur
    (by decide) rev183_s0_ll_mem rev183_s0_lr_mem rev183_s0_ul_mem rev183_s0_ur_mem p
    (hp _ rev183_plane44_mem) (hp _ rev183_plane3_mem) hx0 hx1
def rev183_s1_ll : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev183_s1_ll_mem : rev183_s1_ll.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane17 rev183_vertex2 rev183_vertex0 rev183_s1_ll
    rev183_vertex2_mem rev183_vertex0_mem (by decide)
def rev183_s1_lr : FractionPoint := ⟨1248440601,4638800000,1,1⟩
theorem rev183_s1_lr_mem : rev183_s1_lr.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane17 rev183_vertex2 rev183_vertex0 rev183_s1_lr
    rev183_vertex2_mem rev183_vertex0_mem (by decide)
def rev183_s1_ul : FractionPoint := ⟨127407110603973,478882946000000,1,1⟩
theorem rev183_s1_ul_mem : rev183_s1_ul.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane3 rev183_vertex1 rev183_vertex0 rev183_s1_ul
    rev183_vertex1_mem rev183_vertex0_mem (by decide)
def rev183_s1_ur : FractionPoint := ⟨1248440601,4638800000,1,1⟩
theorem rev183_s1_ur_mem : rev183_s1_ur.real ∈ rationalHull (fractionRow183.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow183 rev183_plane3 rev183_vertex1 rev183_vertex0 rev183_s1_ur
    rev183_vertex1_mem rev183_vertex0_mem (by decide)
theorem rev183_slab1 (p : Point) (hp : p∈IntegerCarrier rev183_planes)
    (hx0 : rev183_s1_ll.real.1≤p.1) (hx1 : p.1≤rev183_s1_lr.real.1) :
    p∈rationalHull (fractionRow183.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev183_plane17 rev183_plane3 rev183_s1_ll rev183_s1_lr rev183_s1_ul rev183_s1_ur
    (by decide) rev183_s1_ll_mem rev183_s1_lr_mem rev183_s1_ul_mem rev183_s1_ur_mem p
    (hp _ rev183_plane17_mem) (hp _ rev183_plane3_mem) hx0 hx1
theorem rev183_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev183_planes) : rev183_s0_ll.real.1≤p.1 := by
  have hc := rev183_plane3.combine_sound rev183_plane44 15204000000 1 (by decide) (by decide) p
    (hp _ rev183_plane3_mem) (hp _ rev183_plane44_mem)
  exact (rev183_plane3.combine rev183_plane44 15204000000 1).xBoundCheck_sound rev183_s0_ll.nx rev183_s0_ll.dx true (by decide) p hc
theorem rev183_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev183_planes) : p.1≤rev183_s1_lr.real.1 := by
  have hc := rev183_plane3.combine_sound rev183_plane17 287616000000 1 (by decide) (by decide) p
    (hp _ rev183_plane3_mem) (hp _ rev183_plane17_mem)
  exact (rev183_plane3.combine rev183_plane17 287616000000 1).xBoundCheck_sound rev183_s1_lr.nx rev183_s1_lr.dx false (by decide) p hc
theorem rev183_hull (p : Point) (hp : p∈IntegerCarrier rev183_planes) :
    p∈rationalHull (fractionRow183.map FractionPoint.rational) := by
  have hxlo := rev183_bound0_lo p hp
  have hxhi := rev183_bound0_hi p hp
  by_cases h0 : p.1≤rev183_s0_lr.real.1
  · exact rev183_slab0 p hp hxlo h0
  exact rev183_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull183 (p : Point)
    (hp : ∀ g, ClosedCell ((![12,14,4,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow183 := by
  rw [← fractionRow183_correct]
  exact rev183_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull183
