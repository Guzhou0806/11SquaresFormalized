import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev124_planes : List IntegerPlane := integerOverlayPlanes ![8,15,5,2]
def rev124_plane34 : IntegerPlane := ⟨2129316000000,(-1440116000000),(-612143880216)⟩
theorem rev124_plane34_mem : rev124_plane34 ∈ rev124_planes := by decide
def rev124_plane35 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-1570721771568)⟩
theorem rev124_plane35_mem : rev124_plane35 ∈ rev124_planes := by decide
def rev124_plane44 : IntegerPlane := ⟨(-1440116000000),2129316000000,1301343880216⟩
theorem rev124_plane44_mem : rev124_plane44 ∈ rev124_planes := by decide
def rev124_plane67 : IntegerPlane := ⟨(-287616000000),1855520000000,1356143759600⟩
theorem rev124_plane67_mem : rev124_plane67 ∈ rev124_planes := by decide
def rev124_vertex0 : FractionPoint := fractionRow124[0]!
theorem rev124_vertex0_mem : rev124_vertex0∈fractionRow124 := by decide
def rev124_vertex1 : FractionPoint := fractionRow124[1]!
theorem rev124_vertex1_mem : rev124_vertex1∈fractionRow124 := by decide
def rev124_vertex2 : FractionPoint := fractionRow124[2]!
theorem rev124_vertex2_mem : rev124_vertex2∈fractionRow124 := by decide
def rev124_vertex3 : FractionPoint := fractionRow124[3]!
theorem rev124_vertex3_mem : rev124_vertex3∈fractionRow124 := by decide
def rev124_s0_ll : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev124_s0_ll_mem : rev124_s0_ll.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane35 rev124_vertex0 rev124_vertex1 rev124_s0_ll
    rev124_vertex0_mem rev124_vertex1_mem (by decide)
def rev124_s0_lr : FractionPoint := ⟨431262268381943,2073350951000000,216994696901067,296192993000000⟩
theorem rev124_s0_lr_mem : rev124_s0_lr.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane35 rev124_vertex0 rev124_vertex1 rev124_s0_lr
    rev124_vertex0_mem rev124_vertex1_mem (by decide)
def rev124_s0_ul : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev124_s0_ul_mem : rev124_s0_ul.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane44 rev124_vertex0 rev124_vertex3 rev124_s0_ul
    rev124_vertex0_mem rev124_vertex3_mem (by decide)
def rev124_s0_ur : FractionPoint := ⟨431262268381943,2073350951000000,276600855376416992567,367901612798293000000⟩
theorem rev124_s0_ur_mem : rev124_s0_ur.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane44 rev124_vertex0 rev124_vertex3 rev124_s0_ur
    rev124_vertex0_mem rev124_vertex3_mem (by decide)
theorem rev124_slab0 (p : Point) (hp : p∈IntegerCarrier rev124_planes)
    (hx0 : rev124_s0_ll.real.1≤p.1) (hx1 : p.1≤rev124_s0_lr.real.1) :
    p∈rationalHull (fractionRow124.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev124_plane35 rev124_plane44 rev124_s0_ll rev124_s0_lr rev124_s0_ul rev124_s0_ur
    (by decide) rev124_s0_ll_mem rev124_s0_lr_mem rev124_s0_ul_mem rev124_s0_ur_mem p
    (hp _ rev124_plane35_mem) (hp _ rev124_plane44_mem) hx0 hx1
def rev124_s1_ll : FractionPoint := ⟨431262268381943,2073350951000000,216994696901067,296192993000000⟩
theorem rev124_s1_ll_mem : rev124_s1_ll.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane34 rev124_vertex1 rev124_vertex2 rev124_s1_ll
    rev124_vertex1_mem rev124_vertex2_mem (by decide)
def rev124_s1_lr : FractionPoint := ⟨1478090653118879,6436683405200000,8859373040646928435359,11586963448453754000000⟩
theorem rev124_s1_lr_mem : rev124_s1_lr.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane34 rev124_vertex1 rev124_vertex2 rev124_s1_lr
    rev124_vertex1_mem rev124_vertex2_mem (by decide)
def rev124_s1_ul : FractionPoint := ⟨431262268381943,2073350951000000,276600855376416992567,367901612798293000000⟩
theorem rev124_s1_ul_mem : rev124_s1_ul.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane44 rev124_vertex0 rev124_vertex3 rev124_s1_ul
    rev124_vertex0_mem rev124_vertex3_mem (by decide)
def rev124_s1_ur : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev124_s1_ur_mem : rev124_s1_ur.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane44 rev124_vertex0 rev124_vertex3 rev124_s1_ur
    rev124_vertex0_mem rev124_vertex3_mem (by decide)
theorem rev124_slab1 (p : Point) (hp : p∈IntegerCarrier rev124_planes)
    (hx0 : rev124_s1_ll.real.1≤p.1) (hx1 : p.1≤rev124_s1_lr.real.1) :
    p∈rationalHull (fractionRow124.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev124_plane34 rev124_plane44 rev124_s1_ll rev124_s1_lr rev124_s1_ul rev124_s1_ur
    (by decide) rev124_s1_ll_mem rev124_s1_lr_mem rev124_s1_ul_mem rev124_s1_ur_mem p
    (hp _ rev124_plane34_mem) (hp _ rev124_plane44_mem) hx0 hx1
def rev124_s2_ll : FractionPoint := ⟨1478090653118879,6436683405200000,8859373040646928435359,11586963448453754000000⟩
theorem rev124_s2_ll_mem : rev124_s2_ll.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane34 rev124_vertex1 rev124_vertex2 rev124_s2_ll
    rev124_vertex1_mem rev124_vertex2_mem (by decide)
def rev124_s2_lr : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev124_s2_lr_mem : rev124_s2_lr.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane34 rev124_vertex1 rev124_vertex2 rev124_s2_lr
    rev124_vertex1_mem rev124_vertex2_mem (by decide)
def rev124_s2_ul : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev124_s2_ul_mem : rev124_s2_ul.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane67 rev124_vertex3 rev124_vertex2 rev124_s2_ul
    rev124_vertex3_mem rev124_vertex2_mem (by decide)
def rev124_s2_ur : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev124_s2_ur_mem : rev124_s2_ur.real ∈ rationalHull (fractionRow124.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow124 rev124_plane67 rev124_vertex3 rev124_vertex2 rev124_s2_ur
    rev124_vertex3_mem rev124_vertex2_mem (by decide)
theorem rev124_slab2 (p : Point) (hp : p∈IntegerCarrier rev124_planes)
    (hx0 : rev124_s2_ll.real.1≤p.1) (hx1 : p.1≤rev124_s2_lr.real.1) :
    p∈rationalHull (fractionRow124.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev124_plane34 rev124_plane67 rev124_s2_ll rev124_s2_lr rev124_s2_ul rev124_s2_ur
    (by decide) rev124_s2_ll_mem rev124_s2_lr_mem rev124_s2_ul_mem rev124_s2_ur_mem p
    (hp _ rev124_plane34_mem) (hp _ rev124_plane67_mem) hx0 hx1
theorem rev124_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev124_planes) : rev124_s0_ll.real.1≤p.1 := by
  have hc := rev124_plane35.combine_sound rev124_plane44 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev124_plane35_mem) (hp _ rev124_plane44_mem)
  exact (rev124_plane35.combine rev124_plane44 2129316000000 2139684000000).xBoundCheck_sound rev124_s0_ll.nx rev124_s0_ll.dx true (by decide) p hc
theorem rev124_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev124_planes) : p.1≤rev124_s2_lr.real.1 := by
  have hc := rev124_plane34.combine_sound rev124_plane67 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev124_plane34_mem) (hp _ rev124_plane67_mem)
  exact (rev124_plane34.combine rev124_plane67 1855520000000 1440116000000).xBoundCheck_sound rev124_s2_lr.nx rev124_s2_lr.dx false (by decide) p hc
theorem rev124_hull (p : Point) (hp : p∈IntegerCarrier rev124_planes) :
    p∈rationalHull (fractionRow124.map FractionPoint.rational) := by
  have hxlo := rev124_bound0_lo p hp
  have hxhi := rev124_bound0_hi p hp
  by_cases h0 : p.1≤rev124_s0_lr.real.1
  · exact rev124_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev124_s1_lr.real.1
  · exact rev124_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev124_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull124 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow124 := by
  rw [← fractionRow124_correct]
  exact rev124_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull124
