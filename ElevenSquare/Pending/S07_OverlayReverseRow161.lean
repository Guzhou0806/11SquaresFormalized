import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev161_planes : List IntegerPlane := integerOverlayPlanes ![10,13,8,15]
def rev161_plane19 : IntegerPlane := ⟨2129316000000,1440116000000,2741459880216⟩
theorem rev161_plane19_mem : rev161_plane19 ∈ rev161_planes := by decide
def rev161_plane36 : IntegerPlane := ⟨1855520000000,287616000000,1643759759600⟩
theorem rev161_plane36_mem : rev161_plane36 ∈ rev161_planes := by decide
def rev161_plane74 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-2741459880216)⟩
theorem rev161_plane74_mem : rev161_plane74 ∈ rev161_planes := by decide
def rev161_plane75 : IntegerPlane := ⟨(-2139684000000),15204000000,(-1555517771568)⟩
theorem rev161_plane75_mem : rev161_plane75 ∈ rev161_planes := by decide
def rev161_vertex0 : FractionPoint := fractionRow161[0]!
theorem rev161_vertex0_mem : rev161_vertex0∈fractionRow161 := by decide
def rev161_vertex1 : FractionPoint := fractionRow161[1]!
theorem rev161_vertex1_mem : rev161_vertex1∈fractionRow161 := by decide
def rev161_vertex2 : FractionPoint := fractionRow161[2]!
theorem rev161_vertex2_mem : rev161_vertex2∈fractionRow161 := by decide
def rev161_vertex3 : FractionPoint := fractionRow161[3]!
theorem rev161_vertex3_mem : rev161_vertex3∈fractionRow161 := by decide
def rev161_s0_ll : FractionPoint := ⟨216994696901067,296192993000000,1642088682618057,2073350951000000⟩
theorem rev161_s0_ll_mem : rev161_s0_ll.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane74 rev161_vertex3 rev161_vertex0 rev161_s0_ll
    rev161_vertex3_mem rev161_vertex0_mem (by decide)
def rev161_s0_lr : FractionPoint := ⟨23768824866023187,32435075873000000,4557466185569466971573,5755377168132739000000⟩
theorem rev161_s0_lr_mem : rev161_s0_lr.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane74 rev161_vertex3 rev161_vertex0 rev161_s0_lr
    rev161_vertex3_mem rev161_vertex0_mem (by decide)
def rev161_s0_ul : FractionPoint := ⟨216994696901067,296192993000000,1642088682618057,2073350951000000⟩
theorem rev161_s0_ul_mem : rev161_s0_ul.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane75 rev161_vertex3 rev161_vertex2 rev161_s0_ul
    rev161_vertex3_mem rev161_vertex2_mem (by decide)
def rev161_s0_ur : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev161_s0_ur_mem : rev161_s0_ur.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane75 rev161_vertex3 rev161_vertex2 rev161_s0_ur
    rev161_vertex3_mem rev161_vertex2_mem (by decide)
theorem rev161_slab0 (p : Point) (hp : p∈IntegerCarrier rev161_planes)
    (hx0 : rev161_s0_ll.real.1≤p.1) (hx1 : p.1≤rev161_s0_lr.real.1) :
    p∈rationalHull (fractionRow161.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev161_plane74 rev161_plane75 rev161_s0_ll rev161_s0_lr rev161_s0_ul rev161_s0_ur
    (by decide) rev161_s0_ll_mem rev161_s0_lr_mem rev161_s0_ul_mem rev161_s0_ur_mem p
    (hp _ rev161_plane74_mem) (hp _ rev161_plane75_mem) hx0 hx1
def rev161_s1_ll : FractionPoint := ⟨23768824866023187,32435075873000000,4557466185569466971573,5755377168132739000000⟩
theorem rev161_s1_ll_mem : rev161_s1_ll.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane74 rev161_vertex3 rev161_vertex0 rev161_s1_ll
    rev161_vertex3_mem rev161_vertex0_mem (by decide)
def rev161_s1_lr : FractionPoint := ⟨24667453203873571,32183417026000000,2635277627344497169169,3426433240406710800000⟩
theorem rev161_s1_lr_mem : rev161_s1_lr.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane74 rev161_vertex3 rev161_vertex0 rev161_s1_lr
    rev161_vertex3_mem rev161_vertex0_mem (by decide)
def rev161_s1_ul : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev161_s1_ul_mem : rev161_s1_ul.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane19 rev161_vertex2 rev161_vertex1 rev161_s1_ul
    rev161_vertex2_mem rev161_vertex1_mem (by decide)
def rev161_s1_ur : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev161_s1_ur_mem : rev161_s1_ur.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane19 rev161_vertex2 rev161_vertex1 rev161_s1_ur
    rev161_vertex2_mem rev161_vertex1_mem (by decide)
theorem rev161_slab1 (p : Point) (hp : p∈IntegerCarrier rev161_planes)
    (hx0 : rev161_s1_ll.real.1≤p.1) (hx1 : p.1≤rev161_s1_lr.real.1) :
    p∈rationalHull (fractionRow161.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev161_plane74 rev161_plane19 rev161_s1_ll rev161_s1_lr rev161_s1_ul rev161_s1_ur
    (by decide) rev161_s1_ll_mem rev161_s1_lr_mem rev161_s1_ul_mem rev161_s1_ur_mem p
    (hp _ rev161_plane74_mem) (hp _ rev161_plane19_mem) hx0 hx1
def rev161_s2_ll : FractionPoint := ⟨24667453203873571,32183417026000000,2635277627344497169169,3426433240406710800000⟩
theorem rev161_s2_ll_mem : rev161_s2_ll.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane74 rev161_vertex3 rev161_vertex0 rev161_s2_ll
    rev161_vertex3_mem rev161_vertex0_mem (by decide)
def rev161_s2_lr : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev161_s2_lr_mem : rev161_s2_lr.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane74 rev161_vertex3 rev161_vertex0 rev161_s2_lr
    rev161_vertex3_mem rev161_vertex0_mem (by decide)
def rev161_s2_ul : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev161_s2_ul_mem : rev161_s2_ul.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane36 rev161_vertex1 rev161_vertex0 rev161_s2_ul
    rev161_vertex1_mem rev161_vertex0_mem (by decide)
def rev161_s2_ur : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev161_s2_ur_mem : rev161_s2_ur.real ∈ rationalHull (fractionRow161.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow161 rev161_plane36 rev161_vertex1 rev161_vertex0 rev161_s2_ur
    rev161_vertex1_mem rev161_vertex0_mem (by decide)
theorem rev161_slab2 (p : Point) (hp : p∈IntegerCarrier rev161_planes)
    (hx0 : rev161_s2_ll.real.1≤p.1) (hx1 : p.1≤rev161_s2_lr.real.1) :
    p∈rationalHull (fractionRow161.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev161_plane74 rev161_plane36 rev161_s2_ll rev161_s2_lr rev161_s2_ul rev161_s2_ur
    (by decide) rev161_s2_ll_mem rev161_s2_lr_mem rev161_s2_ul_mem rev161_s2_ur_mem p
    (hp _ rev161_plane74_mem) (hp _ rev161_plane36_mem) hx0 hx1
theorem rev161_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev161_planes) : rev161_s0_ll.real.1≤p.1 := by
  have hc := rev161_plane74.combine_sound rev161_plane75 15204000000 2129316000000 (by decide) (by decide) p
    (hp _ rev161_plane74_mem) (hp _ rev161_plane75_mem)
  exact (rev161_plane74.combine rev161_plane75 15204000000 2129316000000).xBoundCheck_sound rev161_s0_ll.nx rev161_s0_ll.dx true (by decide) p hc
theorem rev161_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev161_planes) : p.1≤rev161_s2_lr.real.1 := by
  have hc := rev161_plane36.combine_sound rev161_plane74 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev161_plane36_mem) (hp _ rev161_plane74_mem)
  exact (rev161_plane36.combine rev161_plane74 2129316000000 287616000000).xBoundCheck_sound rev161_s2_lr.nx rev161_s2_lr.dx false (by decide) p hc
theorem rev161_hull (p : Point) (hp : p∈IntegerCarrier rev161_planes) :
    p∈rationalHull (fractionRow161.map FractionPoint.rational) := by
  have hxlo := rev161_bound0_lo p hp
  have hxhi := rev161_bound0_hi p hp
  by_cases h0 : p.1≤rev161_s0_lr.real.1
  · exact rev161_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev161_s1_lr.real.1
  · exact rev161_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev161_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull161 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow161 := by
  rw [← fractionRow161_correct]
  exact rev161_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull161
