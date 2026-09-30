import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev186_planes : List IntegerPlane := integerOverlayPlanes ![13,10,0,7]
def rev186_plane16 : IntegerPlane := ⟨(-1855520000000),287616000000,(-211760240400)⟩
theorem rev186_plane16_mem : rev186_plane16 ∈ rev186_planes := by decide
def rev186_plane39 : IntegerPlane := ⟨(-2129316000000),1440116000000,612143880216⟩
theorem rev186_plane39_mem : rev186_plane39 ∈ rev186_planes := by decide
def rev186_plane48 : IntegerPlane := ⟨2139684000000,15204000000,584166228432⟩
theorem rev186_plane48_mem : rev186_plane48 ∈ rev186_planes := by decide
def rev186_plane49 : IntegerPlane := ⟨1440116000000,(-2129316000000),(-1301343880216)⟩
theorem rev186_plane49_mem : rev186_plane49 ∈ rev186_planes := by decide
def rev186_vertex0 : FractionPoint := fractionRow186[0]!
theorem rev186_vertex0_mem : rev186_vertex0∈fractionRow186 := by decide
def rev186_vertex1 : FractionPoint := fractionRow186[1]!
theorem rev186_vertex1_mem : rev186_vertex1∈fractionRow186 := by decide
def rev186_vertex2 : FractionPoint := fractionRow186[2]!
theorem rev186_vertex2_mem : rev186_vertex2∈fractionRow186 := by decide
def rev186_vertex3 : FractionPoint := fractionRow186[3]!
theorem rev186_vertex3_mem : rev186_vertex3∈fractionRow186 := by decide
def rev186_s0_ll : FractionPoint := ⟨613981986234949,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev186_s0_ll_mem : rev186_s0_ll.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane49 rev186_vertex2 rev186_vertex3 rev186_s0_ll
    rev186_vertex2_mem rev186_vertex3_mem (by decide)
def rev186_s0_lr : FractionPoint := ⟨7515963822126429,32183417026000000,2635277627344497169169,3426433240406710800000⟩
theorem rev186_s0_lr_mem : rev186_s0_lr.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane49 rev186_vertex2 rev186_vertex3 rev186_s0_lr
    rev186_vertex2_mem rev186_vertex3_mem (by decide)
def rev186_s0_ul : FractionPoint := ⟨613981986234949,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev186_s0_ul_mem : rev186_s0_ul.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane16 rev186_vertex2 rev186_vertex1 rev186_s0_ul
    rev186_vertex2_mem rev186_vertex1_mem (by decide)
def rev186_s0_ur : FractionPoint := ⟨7515963822126429,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev186_s0_ur_mem : rev186_s0_ur.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane16 rev186_vertex2 rev186_vertex1 rev186_s0_ur
    rev186_vertex2_mem rev186_vertex1_mem (by decide)
theorem rev186_slab0 (p : Point) (hp : p∈IntegerCarrier rev186_planes)
    (hx0 : rev186_s0_ll.real.1≤p.1) (hx1 : p.1≤rev186_s0_lr.real.1) :
    p∈rationalHull (fractionRow186.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev186_plane49 rev186_plane16 rev186_s0_ll rev186_s0_lr rev186_s0_ul rev186_s0_ur
    (by decide) rev186_s0_ll_mem rev186_s0_lr_mem rev186_s0_ul_mem rev186_s0_ur_mem p
    (hp _ rev186_plane49_mem) (hp _ rev186_plane16_mem) hx0 hx1
def rev186_s1_ll : FractionPoint := ⟨7515963822126429,32183417026000000,2635277627344497169169,3426433240406710800000⟩
theorem rev186_s1_ll_mem : rev186_s1_ll.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane49 rev186_vertex2 rev186_vertex3 rev186_s1_ll
    rev186_vertex2_mem rev186_vertex3_mem (by decide)
def rev186_s1_lr : FractionPoint := ⟨8666251006976813,32435075873000000,4557466185569466971573,5755377168132739000000⟩
theorem rev186_s1_lr_mem : rev186_s1_lr.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane49 rev186_vertex2 rev186_vertex3 rev186_s1_lr
    rev186_vertex2_mem rev186_vertex3_mem (by decide)
def rev186_s1_ul : FractionPoint := ⟨7515963822126429,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev186_s1_ul_mem : rev186_s1_ul.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane39 rev186_vertex1 rev186_vertex0 rev186_s1_ul
    rev186_vertex1_mem rev186_vertex0_mem (by decide)
def rev186_s1_ur : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev186_s1_ur_mem : rev186_s1_ur.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane39 rev186_vertex1 rev186_vertex0 rev186_s1_ur
    rev186_vertex1_mem rev186_vertex0_mem (by decide)
theorem rev186_slab1 (p : Point) (hp : p∈IntegerCarrier rev186_planes)
    (hx0 : rev186_s1_ll.real.1≤p.1) (hx1 : p.1≤rev186_s1_lr.real.1) :
    p∈rationalHull (fractionRow186.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev186_plane49 rev186_plane39 rev186_s1_ll rev186_s1_lr rev186_s1_ul rev186_s1_ur
    (by decide) rev186_s1_ll_mem rev186_s1_lr_mem rev186_s1_ul_mem rev186_s1_ur_mem p
    (hp _ rev186_plane49_mem) (hp _ rev186_plane39_mem) hx0 hx1
def rev186_s2_ll : FractionPoint := ⟨8666251006976813,32435075873000000,4557466185569466971573,5755377168132739000000⟩
theorem rev186_s2_ll_mem : rev186_s2_ll.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane49 rev186_vertex2 rev186_vertex3 rev186_s2_ll
    rev186_vertex2_mem rev186_vertex3_mem (by decide)
def rev186_s2_lr : FractionPoint := ⟨79198296098933,296192993000000,1642088682618057,2073350951000000⟩
theorem rev186_s2_lr_mem : rev186_s2_lr.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane49 rev186_vertex2 rev186_vertex3 rev186_s2_lr
    rev186_vertex2_mem rev186_vertex3_mem (by decide)
def rev186_s2_ul : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev186_s2_ul_mem : rev186_s2_ul.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane48 rev186_vertex0 rev186_vertex3 rev186_s2_ul
    rev186_vertex0_mem rev186_vertex3_mem (by decide)
def rev186_s2_ur : FractionPoint := ⟨79198296098933,296192993000000,1642088682618057,2073350951000000⟩
theorem rev186_s2_ur_mem : rev186_s2_ur.real ∈ rationalHull (fractionRow186.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow186 rev186_plane48 rev186_vertex0 rev186_vertex3 rev186_s2_ur
    rev186_vertex0_mem rev186_vertex3_mem (by decide)
theorem rev186_slab2 (p : Point) (hp : p∈IntegerCarrier rev186_planes)
    (hx0 : rev186_s2_ll.real.1≤p.1) (hx1 : p.1≤rev186_s2_lr.real.1) :
    p∈rationalHull (fractionRow186.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev186_plane49 rev186_plane48 rev186_s2_ll rev186_s2_lr rev186_s2_ul rev186_s2_ur
    (by decide) rev186_s2_ll_mem rev186_s2_lr_mem rev186_s2_ul_mem rev186_s2_ur_mem p
    (hp _ rev186_plane49_mem) (hp _ rev186_plane48_mem) hx0 hx1
theorem rev186_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev186_planes) : rev186_s0_ll.real.1≤p.1 := by
  have hc := rev186_plane16.combine_sound rev186_plane49 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev186_plane16_mem) (hp _ rev186_plane49_mem)
  exact (rev186_plane16.combine rev186_plane49 2129316000000 287616000000).xBoundCheck_sound rev186_s0_ll.nx rev186_s0_ll.dx true (by decide) p hc
theorem rev186_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev186_planes) : p.1≤rev186_s2_lr.real.1 := by
  have hc := rev186_plane48.combine_sound rev186_plane49 2129316000000 15204000000 (by decide) (by decide) p
    (hp _ rev186_plane48_mem) (hp _ rev186_plane49_mem)
  exact (rev186_plane48.combine rev186_plane49 2129316000000 15204000000).xBoundCheck_sound rev186_s2_lr.nx rev186_s2_lr.dx false (by decide) p hc
theorem rev186_hull (p : Point) (hp : p∈IntegerCarrier rev186_planes) :
    p∈rationalHull (fractionRow186.map FractionPoint.rational) := by
  have hxlo := rev186_bound0_lo p hp
  have hxhi := rev186_bound0_hi p hp
  by_cases h0 : p.1≤rev186_s0_lr.real.1
  · exact rev186_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev186_s1_lr.real.1
  · exact rev186_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev186_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull186 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,0,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow186 := by
  rw [← fractionRow186_correct]
  exact rev186_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull186
