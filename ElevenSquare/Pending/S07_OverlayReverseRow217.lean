import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks27
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev217_planes : List IntegerPlane := integerOverlayPlanes ![15,12,12,15]
def rev217_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev217_plane1_mem : rev217_plane1 ∈ rev217_planes := by decide
def rev217_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev217_plane3_mem : rev217_plane3 ∈ rev217_planes := by decide
def rev217_plane32 : IntegerPlane := ⟨202532000000,(-1861776000000),(-1275872260553)⟩
theorem rev217_plane32_mem : rev217_plane32 ∈ rev217_planes := by decide
def rev217_plane52 : IntegerPlane := ⟨(-1861776000000),202532000000,(-1275872260553)⟩
theorem rev217_plane52_mem : rev217_plane52 ∈ rev217_planes := by decide
def rev217_vertex0 : FractionPoint := fractionRow217[0]!
theorem rev217_vertex0_mem : rev217_vertex0∈fractionRow217 := by decide
def rev217_vertex1 : FractionPoint := fractionRow217[1]!
theorem rev217_vertex1_mem : rev217_vertex1∈fractionRow217 := by decide
def rev217_vertex2 : FractionPoint := fractionRow217[2]!
theorem rev217_vertex2_mem : rev217_vertex2∈fractionRow217 := by decide
def rev217_vertex3 : FractionPoint := fractionRow217[3]!
theorem rev217_vertex3_mem : rev217_vertex3∈fractionRow217 := by decide
def rev217_s0_ll : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev217_s0_ll_mem : rev217_s0_ll.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane32 rev217_vertex3 rev217_vertex0 rev217_s0_ll
    rev217_vertex3_mem rev217_vertex0_mem (by decide)
def rev217_s0_lr : FractionPoint := ⟨1478404260553,1861776000000,668703131365410581,866552468544000000⟩
theorem rev217_s0_lr_mem : rev217_s0_lr.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane32 rev217_vertex3 rev217_vertex0 rev217_s0_lr
    rev217_vertex3_mem rev217_vertex0_mem (by decide)
def rev217_s0_ul : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev217_s0_ul_mem : rev217_s0_ul.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane52 rev217_vertex3 rev217_vertex2 rev217_s0_ul
    rev217_vertex3_mem rev217_vertex2_mem (by decide)
def rev217_s0_ur : FractionPoint := ⟨1478404260553,1861776000000,1,1⟩
theorem rev217_s0_ur_mem : rev217_s0_ur.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane52 rev217_vertex3 rev217_vertex2 rev217_s0_ur
    rev217_vertex3_mem rev217_vertex2_mem (by decide)
theorem rev217_slab0 (p : Point) (hp : p∈IntegerCarrier rev217_planes)
    (hx0 : rev217_s0_ll.real.1≤p.1) (hx1 : p.1≤rev217_s0_lr.real.1) :
    p∈rationalHull (fractionRow217.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev217_plane32 rev217_plane52 rev217_s0_ll rev217_s0_lr rev217_s0_ul rev217_s0_ur
    (by decide) rev217_s0_ll_mem rev217_s0_lr_mem rev217_s0_ul_mem rev217_s0_ur_mem p
    (hp _ rev217_plane32_mem) (hp _ rev217_plane52_mem) hx0 hx1
def rev217_s1_ll : FractionPoint := ⟨1478404260553,1861776000000,668703131365410581,866552468544000000⟩
theorem rev217_s1_ll_mem : rev217_s1_ll.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane32 rev217_vertex3 rev217_vertex0 rev217_s1_ll
    rev217_vertex3_mem rev217_vertex0_mem (by decide)
def rev217_s1_lr : FractionPoint := ⟨1,1,1478404260553,1861776000000⟩
theorem rev217_s1_lr_mem : rev217_s1_lr.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane32 rev217_vertex3 rev217_vertex0 rev217_s1_lr
    rev217_vertex3_mem rev217_vertex0_mem (by decide)
def rev217_s1_ul : FractionPoint := ⟨1478404260553,1861776000000,1,1⟩
theorem rev217_s1_ul_mem : rev217_s1_ul.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane3 rev217_vertex2 rev217_vertex1 rev217_s1_ul
    rev217_vertex2_mem rev217_vertex1_mem (by decide)
def rev217_s1_ur : FractionPoint := ⟨1,1,1,1⟩
theorem rev217_s1_ur_mem : rev217_s1_ur.real ∈ rationalHull (fractionRow217.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow217 rev217_plane3 rev217_vertex2 rev217_vertex1 rev217_s1_ur
    rev217_vertex2_mem rev217_vertex1_mem (by decide)
theorem rev217_slab1 (p : Point) (hp : p∈IntegerCarrier rev217_planes)
    (hx0 : rev217_s1_ll.real.1≤p.1) (hx1 : p.1≤rev217_s1_lr.real.1) :
    p∈rationalHull (fractionRow217.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev217_plane32 rev217_plane3 rev217_s1_ll rev217_s1_lr rev217_s1_ul rev217_s1_ur
    (by decide) rev217_s1_ll_mem rev217_s1_lr_mem rev217_s1_ul_mem rev217_s1_ur_mem p
    (hp _ rev217_plane32_mem) (hp _ rev217_plane3_mem) hx0 hx1
theorem rev217_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev217_planes) : rev217_s0_ll.real.1≤p.1 := by
  have hc := rev217_plane32.combine_sound rev217_plane52 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev217_plane32_mem) (hp _ rev217_plane52_mem)
  exact (rev217_plane32.combine rev217_plane52 202532000000 1861776000000).xBoundCheck_sound rev217_s0_ll.nx rev217_s0_ll.dx true (by decide) p hc
theorem rev217_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev217_planes) : p.1≤rev217_s1_lr.real.1 := by
  have hc := rev217_plane1.combine_sound rev217_plane1 1 0 (by decide) (by decide) p
    (hp _ rev217_plane1_mem) (hp _ rev217_plane1_mem)
  exact (rev217_plane1.combine rev217_plane1 1 0).xBoundCheck_sound rev217_s1_lr.nx rev217_s1_lr.dx false (by decide) p hc
theorem rev217_hull (p : Point) (hp : p∈IntegerCarrier rev217_planes) :
    p∈rationalHull (fractionRow217.map FractionPoint.rational) := by
  have hxlo := rev217_bound0_lo p hp
  have hxhi := rev217_bound0_hi p hp
  by_cases h0 : p.1≤rev217_s0_lr.real.1
  · exact rev217_slab0 p hp hxlo h0
  exact rev217_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull217 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,12,12,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow217 := by
  rw [← fractionRow217_correct]
  exact rev217_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull217
