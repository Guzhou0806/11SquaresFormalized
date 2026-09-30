import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks27
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev218_planes : List IntegerPlane := integerOverlayPlanes ![15,13,8,11]
def rev218_plane14 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-2741459880216)⟩
theorem rev218_plane14_mem : rev218_plane14 ∈ rev218_planes := by decide
def rev218_plane18 : IntegerPlane := ⟨(-2145688000000),699324000000,(-995724727641)⟩
theorem rev218_plane18_mem : rev218_plane18 ∈ rev218_planes := by decide
def rev218_plane79 : IntegerPlane := ⟨2139684000000,(-15204000000),1555517771568⟩
theorem rev218_plane79_mem : rev218_plane79 ∈ rev218_planes := by decide
def rev218_vertex0 : FractionPoint := fractionRow218[0]!
theorem rev218_vertex0_mem : rev218_vertex0∈fractionRow218 := by decide
def rev218_vertex1 : FractionPoint := fractionRow218[1]!
theorem rev218_vertex1_mem : rev218_vertex1∈fractionRow218 := by decide
def rev218_vertex2 : FractionPoint := fractionRow218[2]!
theorem rev218_vertex2_mem : rev218_vertex2∈fractionRow218 := by decide
def rev218_s0_ll : FractionPoint := ⟨167556390057181017,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev218_s0_ll_mem : rev218_s0_ll.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane14 rev218_vertex1 rev218_vertex2 rev218_s0_ll
    rev218_vertex1_mem rev218_vertex2_mem (by decide)
def rev218_s0_lr : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev218_s0_lr_mem : rev218_s0_lr.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane14 rev218_vertex1 rev218_vertex2 rev218_s0_lr
    rev218_vertex1_mem rev218_vertex2_mem (by decide)
def rev218_s0_ul : FractionPoint := ⟨167556390057181017,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev218_s0_ul_mem : rev218_s0_ul.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane18 rev218_vertex1 rev218_vertex0 rev218_s0_ul
    rev218_vertex1_mem rev218_vertex0_mem (by decide)
def rev218_s0_ur : FractionPoint := ⟨23768824866023187,32435075873000000,6234691733156488254021,7560875666603284000000⟩
theorem rev218_s0_ur_mem : rev218_s0_ur.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane18 rev218_vertex1 rev218_vertex0 rev218_s0_ur
    rev218_vertex1_mem rev218_vertex0_mem (by decide)
theorem rev218_slab0 (p : Point) (hp : p∈IntegerCarrier rev218_planes)
    (hx0 : rev218_s0_ll.real.1≤p.1) (hx1 : p.1≤rev218_s0_lr.real.1) :
    p∈rationalHull (fractionRow218.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev218_plane14 rev218_plane18 rev218_s0_ll rev218_s0_lr rev218_s0_ul rev218_s0_ur
    (by decide) rev218_s0_ll_mem rev218_s0_lr_mem rev218_s0_ul_mem rev218_s0_ur_mem p
    (hp _ rev218_plane14_mem) (hp _ rev218_plane18_mem) hx0 hx1
def rev218_s1_ll : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev218_s1_ll_mem : rev218_s1_ll.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane79 rev218_vertex2 rev218_vertex0 rev218_s1_ll
    rev218_vertex2_mem rev218_vertex0_mem (by decide)
def rev218_s1_lr : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev218_s1_lr_mem : rev218_s1_lr.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane79 rev218_vertex2 rev218_vertex0 rev218_s1_lr
    rev218_vertex2_mem rev218_vertex0_mem (by decide)
def rev218_s1_ul : FractionPoint := ⟨23768824866023187,32435075873000000,6234691733156488254021,7560875666603284000000⟩
theorem rev218_s1_ul_mem : rev218_s1_ul.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane18 rev218_vertex1 rev218_vertex0 rev218_s1_ul
    rev218_vertex1_mem rev218_vertex0_mem (by decide)
def rev218_s1_ur : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev218_s1_ur_mem : rev218_s1_ur.real ∈ rationalHull (fractionRow218.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow218 rev218_plane18 rev218_vertex1 rev218_vertex0 rev218_s1_ur
    rev218_vertex1_mem rev218_vertex0_mem (by decide)
theorem rev218_slab1 (p : Point) (hp : p∈IntegerCarrier rev218_planes)
    (hx0 : rev218_s1_ll.real.1≤p.1) (hx1 : p.1≤rev218_s1_lr.real.1) :
    p∈rationalHull (fractionRow218.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev218_plane79 rev218_plane18 rev218_s1_ll rev218_s1_lr rev218_s1_ul rev218_s1_ur
    (by decide) rev218_s1_ll_mem rev218_s1_lr_mem rev218_s1_ul_mem rev218_s1_ur_mem p
    (hp _ rev218_plane79_mem) (hp _ rev218_plane18_mem) hx0 hx1
theorem rev218_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev218_planes) : rev218_s0_ll.real.1≤p.1 := by
  have hc := rev218_plane14.combine_sound rev218_plane18 699324000000 1440116000000 (by decide) (by decide) p
    (hp _ rev218_plane14_mem) (hp _ rev218_plane18_mem)
  exact (rev218_plane14.combine rev218_plane18 699324000000 1440116000000).xBoundCheck_sound rev218_s0_ll.nx rev218_s0_ll.dx true (by decide) p hc
theorem rev218_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev218_planes) : p.1≤rev218_s1_lr.real.1 := by
  have hc := rev218_plane18.combine_sound rev218_plane79 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev218_plane18_mem) (hp _ rev218_plane79_mem)
  exact (rev218_plane18.combine rev218_plane79 15204000000 699324000000).xBoundCheck_sound rev218_s1_lr.nx rev218_s1_lr.dx false (by decide) p hc
theorem rev218_hull (p : Point) (hp : p∈IntegerCarrier rev218_planes) :
    p∈rationalHull (fractionRow218.map FractionPoint.rational) := by
  have hxlo := rev218_bound0_lo p hp
  have hxhi := rev218_bound0_hi p hp
  by_cases h0 : p.1≤rev218_s0_lr.real.1
  · exact rev218_slab0 p hp hxlo h0
  exact rev218_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull218 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,13,8,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow218 := by
  rw [← fractionRow218_correct]
  exact rev218_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull218
