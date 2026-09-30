import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev102_planes : List IntegerPlane := integerOverlayPlanes ![7,4,14,12]
def rev102_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev102_plane1_mem : rev102_plane1 ∈ rev102_planes := by decide
def rev102_plane24 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-584166228432)⟩
theorem rev102_plane24_mem : rev102_plane24 ∈ rev102_planes := by decide
def rev102_plane77 : IntegerPlane := ⟨(-287616000000),1855520000000,211760240400⟩
theorem rev102_plane77_mem : rev102_plane77 ∈ rev102_planes := by decide
def rev102_vertex0 : FractionPoint := fractionRow102[0]!
theorem rev102_vertex0_mem : rev102_vertex0∈fractionRow102 := by decide
def rev102_vertex1 : FractionPoint := fractionRow102[1]!
theorem rev102_vertex1_mem : rev102_vertex1∈fractionRow102 := by decide
def rev102_vertex2 : FractionPoint := fractionRow102[2]!
theorem rev102_vertex2_mem : rev102_vertex2∈fractionRow102 := by decide
def rev102_s0_ll : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev102_s0_ll_mem : rev102_s0_ll.real ∈ rationalHull (fractionRow102.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow102 rev102_plane24 rev102_vertex2 rev102_vertex0 rev102_s0_ll
    rev102_vertex2_mem rev102_vertex0_mem (by decide)
def rev102_s0_lr : FractionPoint := ⟨1,1,11853379759,44576750000⟩
theorem rev102_s0_lr_mem : rev102_s0_lr.real ∈ rationalHull (fractionRow102.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow102 rev102_plane24 rev102_vertex2 rev102_vertex0 rev102_s0_lr
    rev102_vertex2_mem rev102_vertex0_mem (by decide)
def rev102_s0_ul : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev102_s0_ul_mem : rev102_s0_ul.real ∈ rationalHull (fractionRow102.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow102 rev102_plane77 rev102_vertex2 rev102_vertex1 rev102_s0_ul
    rev102_vertex2_mem rev102_vertex1_mem (by decide)
def rev102_s0_ur : FractionPoint := ⟨1,1,1248440601,4638800000⟩
theorem rev102_s0_ur_mem : rev102_s0_ur.real ∈ rationalHull (fractionRow102.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow102 rev102_plane77 rev102_vertex2 rev102_vertex1 rev102_s0_ur
    rev102_vertex2_mem rev102_vertex1_mem (by decide)
theorem rev102_slab0 (p : Point) (hp : p∈IntegerCarrier rev102_planes)
    (hx0 : rev102_s0_ll.real.1≤p.1) (hx1 : p.1≤rev102_s0_lr.real.1) :
    p∈rationalHull (fractionRow102.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev102_plane24 rev102_plane77 rev102_s0_ll rev102_s0_lr rev102_s0_ul rev102_s0_ur
    (by decide) rev102_s0_ll_mem rev102_s0_lr_mem rev102_s0_ul_mem rev102_s0_ur_mem p
    (hp _ rev102_plane24_mem) (hp _ rev102_plane77_mem) hx0 hx1
theorem rev102_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev102_planes) : rev102_s0_ll.real.1≤p.1 := by
  have hc := rev102_plane24.combine_sound rev102_plane77 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev102_plane24_mem) (hp _ rev102_plane77_mem)
  exact (rev102_plane24.combine rev102_plane77 1855520000000 2139684000000).xBoundCheck_sound rev102_s0_ll.nx rev102_s0_ll.dx true (by decide) p hc
theorem rev102_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev102_planes) : p.1≤rev102_s0_lr.real.1 := by
  have hc := rev102_plane1.combine_sound rev102_plane1 1 0 (by decide) (by decide) p
    (hp _ rev102_plane1_mem) (hp _ rev102_plane1_mem)
  exact (rev102_plane1.combine rev102_plane1 1 0).xBoundCheck_sound rev102_s0_lr.nx rev102_s0_lr.dx false (by decide) p hc
theorem rev102_hull (p : Point) (hp : p∈IntegerCarrier rev102_planes) :
    p∈rationalHull (fractionRow102.map FractionPoint.rational) := by
  have hxlo := rev102_bound0_lo p hp
  have hxhi := rev102_bound0_hi p hp
  exact rev102_slab0 p hp hxlo hxhi
theorem overlay_in_hull102 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,4,14,12] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow102 := by
  rw [← fractionRow102_correct]
  exact rev102_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull102
