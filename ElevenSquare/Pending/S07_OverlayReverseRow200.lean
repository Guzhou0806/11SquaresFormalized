import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev200_planes : List IntegerPlane := integerOverlayPlanes ![14,12,8,11]
def rev200_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev200_plane3_mem : rev200_plane3 ∈ rev200_planes := by decide
def rev200_plane37 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-1643759759600)⟩
theorem rev200_plane37_mem : rev200_plane37 ∈ rev200_planes := by decide
def rev200_plane79 : IntegerPlane := ⟨2139684000000,(-15204000000),1555517771568⟩
theorem rev200_plane79_mem : rev200_plane79 ∈ rev200_planes := by decide
def rev200_vertex0 : FractionPoint := fractionRow200[0]!
theorem rev200_vertex0_mem : rev200_vertex0∈fractionRow200 := by decide
def rev200_vertex1 : FractionPoint := fractionRow200[1]!
theorem rev200_vertex1_mem : rev200_vertex1∈fractionRow200 := by decide
def rev200_vertex2 : FractionPoint := fractionRow200[2]!
theorem rev200_vertex2_mem : rev200_vertex2∈fractionRow200 := by decide
def rev200_s0_ll : FractionPoint := ⟨3390359399,4638800000,1,1⟩
theorem rev200_s0_ll_mem : rev200_s0_ll.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane37 rev200_vertex1 rev200_vertex2 rev200_s0_ll
    rev200_vertex1_mem rev200_vertex2_mem (by decide)
def rev200_s0_lr : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev200_s0_lr_mem : rev200_s0_lr.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane37 rev200_vertex1 rev200_vertex2 rev200_s0_lr
    rev200_vertex1_mem rev200_vertex2_mem (by decide)
def rev200_s0_ul : FractionPoint := ⟨3390359399,4638800000,1,1⟩
theorem rev200_s0_ul_mem : rev200_s0_ul.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane3 rev200_vertex1 rev200_vertex0 rev200_s0_ul
    rev200_vertex1_mem rev200_vertex0_mem (by decide)
def rev200_s0_ur : FractionPoint := ⟨351475835396027,478882946000000,1,1⟩
theorem rev200_s0_ur_mem : rev200_s0_ur.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane3 rev200_vertex1 rev200_vertex0 rev200_s0_ur
    rev200_vertex1_mem rev200_vertex0_mem (by decide)
theorem rev200_slab0 (p : Point) (hp : p∈IntegerCarrier rev200_planes)
    (hx0 : rev200_s0_ll.real.1≤p.1) (hx1 : p.1≤rev200_s0_lr.real.1) :
    p∈rationalHull (fractionRow200.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev200_plane37 rev200_plane3 rev200_s0_ll rev200_s0_lr rev200_s0_ul rev200_s0_ur
    (by decide) rev200_s0_ll_mem rev200_s0_lr_mem rev200_s0_ul_mem rev200_s0_ur_mem p
    (hp _ rev200_plane37_mem) (hp _ rev200_plane3_mem) hx0 hx1
def rev200_s1_ll : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev200_s1_ll_mem : rev200_s1_ll.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane79 rev200_vertex2 rev200_vertex0 rev200_s1_ll
    rev200_vertex2_mem rev200_vertex0_mem (by decide)
def rev200_s1_lr : FractionPoint := ⟨32723370241,44576750000,1,1⟩
theorem rev200_s1_lr_mem : rev200_s1_lr.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane79 rev200_vertex2 rev200_vertex0 rev200_s1_lr
    rev200_vertex2_mem rev200_vertex0_mem (by decide)
def rev200_s1_ul : FractionPoint := ⟨351475835396027,478882946000000,1,1⟩
theorem rev200_s1_ul_mem : rev200_s1_ul.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane3 rev200_vertex1 rev200_vertex0 rev200_s1_ul
    rev200_vertex1_mem rev200_vertex0_mem (by decide)
def rev200_s1_ur : FractionPoint := ⟨32723370241,44576750000,1,1⟩
theorem rev200_s1_ur_mem : rev200_s1_ur.real ∈ rationalHull (fractionRow200.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow200 rev200_plane3 rev200_vertex1 rev200_vertex0 rev200_s1_ur
    rev200_vertex1_mem rev200_vertex0_mem (by decide)
theorem rev200_slab1 (p : Point) (hp : p∈IntegerCarrier rev200_planes)
    (hx0 : rev200_s1_ll.real.1≤p.1) (hx1 : p.1≤rev200_s1_lr.real.1) :
    p∈rationalHull (fractionRow200.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev200_plane79 rev200_plane3 rev200_s1_ll rev200_s1_lr rev200_s1_ul rev200_s1_ur
    (by decide) rev200_s1_ll_mem rev200_s1_lr_mem rev200_s1_ul_mem rev200_s1_ur_mem p
    (hp _ rev200_plane79_mem) (hp _ rev200_plane3_mem) hx0 hx1
theorem rev200_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev200_planes) : rev200_s0_ll.real.1≤p.1 := by
  have hc := rev200_plane3.combine_sound rev200_plane37 287616000000 1 (by decide) (by decide) p
    (hp _ rev200_plane3_mem) (hp _ rev200_plane37_mem)
  exact (rev200_plane3.combine rev200_plane37 287616000000 1).xBoundCheck_sound rev200_s0_ll.nx rev200_s0_ll.dx true (by decide) p hc
theorem rev200_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev200_planes) : p.1≤rev200_s1_lr.real.1 := by
  have hc := rev200_plane3.combine_sound rev200_plane79 15204000000 1 (by decide) (by decide) p
    (hp _ rev200_plane3_mem) (hp _ rev200_plane79_mem)
  exact (rev200_plane3.combine rev200_plane79 15204000000 1).xBoundCheck_sound rev200_s1_lr.nx rev200_s1_lr.dx false (by decide) p hc
theorem rev200_hull (p : Point) (hp : p∈IntegerCarrier rev200_planes) :
    p∈rationalHull (fractionRow200.map FractionPoint.rational) := by
  have hxlo := rev200_bound0_lo p hp
  have hxhi := rev200_bound0_hi p hp
  by_cases h0 : p.1≤rev200_s0_lr.real.1
  · exact rev200_slab0 p hp hxlo h0
  exact rev200_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull200 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,12,8,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow200 := by
  rw [← fractionRow200_correct]
  exact rev200_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull200
