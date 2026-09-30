import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev12_planes : List IntegerPlane := integerOverlayPlanes ![1,1,7,4]
def rev12_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev12_plane2_mem : rev12_plane2 ∈ rev12_planes := by decide
def rev12_plane26 : IntegerPlane := ⟨(-2083356000000),746024000000,(-965839292059)⟩
theorem rev12_plane26_mem : rev12_plane26 ∈ rev12_planes := by decide
def rev12_plane55 : IntegerPlane := ⟨2112760000000,(-48252000000),982750749085⟩
theorem rev12_plane55_mem : rev12_plane55 ∈ rev12_planes := by decide
def rev12_vertex0 : FractionPoint := fractionRow12[0]!
theorem rev12_vertex0_mem : rev12_vertex0∈fractionRow12 := by decide
def rev12_vertex1 : FractionPoint := fractionRow12[1]!
theorem rev12_vertex1_mem : rev12_vertex1∈fractionRow12 := by decide
def rev12_vertex2 : FractionPoint := fractionRow12[2]!
theorem rev12_vertex2_mem : rev12_vertex2∈fractionRow12 := by decide
def rev12_s0_ll : FractionPoint := ⟨965839292059,2083356000000,0,1⟩
theorem rev12_s0_ll_mem : rev12_s0_ll.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane2 rev12_vertex0 rev12_vertex1 rev12_s0_ll
    rev12_vertex0_mem rev12_vertex1_mem (by decide)
def rev12_s0_lr : FractionPoint := ⟨196550149817,422552000000,0,1⟩
theorem rev12_s0_lr_mem : rev12_s0_lr.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane2 rev12_vertex0 rev12_vertex1 rev12_s0_lr
    rev12_vertex0_mem rev12_vertex1_mem (by decide)
def rev12_s0_ul : FractionPoint := ⟨965839292059,2083356000000,0,1⟩
theorem rev12_s0_ul_mem : rev12_s0_ul.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane26 rev12_vertex0 rev12_vertex2 rev12_s0_ul
    rev12_vertex0_mem rev12_vertex2_mem (by decide)
def rev12_s0_ur : FractionPoint := ⟨196550149817,422552000000,341652346007821,78808483312000000⟩
theorem rev12_s0_ur_mem : rev12_s0_ur.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane26 rev12_vertex0 rev12_vertex2 rev12_s0_ur
    rev12_vertex0_mem rev12_vertex2_mem (by decide)
theorem rev12_slab0 (p : Point) (hp : p∈IntegerCarrier rev12_planes)
    (hx0 : rev12_s0_ll.real.1≤p.1) (hx1 : p.1≤rev12_s0_lr.real.1) :
    p∈rationalHull (fractionRow12.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev12_plane2 rev12_plane26 rev12_s0_ll rev12_s0_lr rev12_s0_ul rev12_s0_ur
    (by decide) rev12_s0_ll_mem rev12_s0_lr_mem rev12_s0_ul_mem rev12_s0_ur_mem p
    (hp _ rev12_plane2_mem) (hp _ rev12_plane26_mem) hx0 hx1
def rev12_s1_ll : FractionPoint := ⟨196550149817,422552000000,0,1⟩
theorem rev12_s1_ll_mem : rev12_s1_ll.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane55 rev12_vertex1 rev12_vertex2 rev12_s1_ll
    rev12_vertex1_mem rev12_vertex2_mem (by decide)
def rev12_s1_lr : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev12_s1_lr_mem : rev12_s1_lr.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane55 rev12_vertex1 rev12_vertex2 rev12_s1_lr
    rev12_vertex1_mem rev12_vertex2_mem (by decide)
def rev12_s1_ul : FractionPoint := ⟨196550149817,422552000000,341652346007821,78808483312000000⟩
theorem rev12_s1_ul_mem : rev12_s1_ul.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane26 rev12_vertex0 rev12_vertex2 rev12_s1_ul
    rev12_vertex0_mem rev12_vertex2_mem (by decide)
def rev12_s1_ur : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev12_s1_ur_mem : rev12_s1_ur.real ∈ rationalHull (fractionRow12.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow12 rev12_plane26 rev12_vertex0 rev12_vertex2 rev12_s1_ur
    rev12_vertex0_mem rev12_vertex2_mem (by decide)
theorem rev12_slab1 (p : Point) (hp : p∈IntegerCarrier rev12_planes)
    (hx0 : rev12_s1_ll.real.1≤p.1) (hx1 : p.1≤rev12_s1_lr.real.1) :
    p∈rationalHull (fractionRow12.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev12_plane55 rev12_plane26 rev12_s1_ll rev12_s1_lr rev12_s1_ul rev12_s1_ur
    (by decide) rev12_s1_ll_mem rev12_s1_lr_mem rev12_s1_ul_mem rev12_s1_ur_mem p
    (hp _ rev12_plane55_mem) (hp _ rev12_plane26_mem) hx0 hx1
theorem rev12_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev12_planes) : rev12_s0_ll.real.1≤p.1 := by
  have hc := rev12_plane2.combine_sound rev12_plane26 746024000000 1 (by decide) (by decide) p
    (hp _ rev12_plane2_mem) (hp _ rev12_plane26_mem)
  exact (rev12_plane2.combine rev12_plane26 746024000000 1).xBoundCheck_sound rev12_s0_ll.nx rev12_s0_ll.dx true (by decide) p hc
theorem rev12_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev12_planes) : p.1≤rev12_s1_lr.real.1 := by
  have hc := rev12_plane26.combine_sound rev12_plane55 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev12_plane26_mem) (hp _ rev12_plane55_mem)
  exact (rev12_plane26.combine rev12_plane55 48252000000 746024000000).xBoundCheck_sound rev12_s1_lr.nx rev12_s1_lr.dx false (by decide) p hc
theorem rev12_hull (p : Point) (hp : p∈IntegerCarrier rev12_planes) :
    p∈rationalHull (fractionRow12.map FractionPoint.rational) := by
  have hxlo := rev12_bound0_lo p hp
  have hxhi := rev12_bound0_hi p hp
  by_cases h0 : p.1≤rev12_s0_lr.real.1
  · exact rev12_slab0 p hp hxlo h0
  exact rev12_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull12 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,1,7,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow12 := by
  rw [← fractionRow12_correct]
  exact rev12_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull12
