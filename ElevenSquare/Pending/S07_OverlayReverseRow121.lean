import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev121_planes : List IntegerPlane := integerOverlayPlanes ![8,15,0,7]
def rev121_plane16 : IntegerPlane := ⟨202532000000,1861776000000,1478404260553⟩
theorem rev121_plane16_mem : rev121_plane16 ∈ rev121_planes := by decide
def rev121_plane34 : IntegerPlane := ⟨2129316000000,(-1440116000000),(-612143880216)⟩
theorem rev121_plane34_mem : rev121_plane34 ∈ rev121_planes := by decide
def rev121_plane49 : IntegerPlane := ⟨1440116000000,(-2129316000000),(-1301343880216)⟩
theorem rev121_plane49_mem : rev121_plane49 ∈ rev121_planes := by decide
def rev121_plane67 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-585903739447)⟩
theorem rev121_plane67_mem : rev121_plane67 ∈ rev121_planes := by decide
def rev121_vertex0 : FractionPoint := fractionRow121[0]!
theorem rev121_vertex0_mem : rev121_vertex0∈fractionRow121 := by decide
def rev121_vertex1 : FractionPoint := fractionRow121[1]!
theorem rev121_vertex1_mem : rev121_vertex1∈fractionRow121 := by decide
def rev121_vertex2 : FractionPoint := fractionRow121[2]!
theorem rev121_vertex2_mem : rev121_vertex2∈fractionRow121 := by decide
def rev121_vertex3 : FractionPoint := fractionRow121[3]!
theorem rev121_vertex3_mem : rev121_vertex3∈fractionRow121 := by decide
def rev121_s0_ll : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev121_s0_ll_mem : rev121_s0_ll.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane67 rev121_vertex3 rev121_vertex0 rev121_s0_ll
    rev121_vertex3_mem rev121_vertex0_mem (by decide)
def rev121_s0_lr : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev121_s0_lr_mem : rev121_s0_lr.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane67 rev121_vertex3 rev121_vertex0 rev121_s0_lr
    rev121_vertex3_mem rev121_vertex0_mem (by decide)
def rev121_s0_ul : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev121_s0_ul_mem : rev121_s0_ul.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane16 rev121_vertex3 rev121_vertex2 rev121_s0_ul
    rev121_vertex3_mem rev121_vertex2_mem (by decide)
def rev121_s0_ur : FractionPoint := ⟨49200521405821067,212798949946400000,190398871400374124151697,247614986147130504000000⟩
theorem rev121_s0_ur_mem : rev121_s0_ur.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane16 rev121_vertex3 rev121_vertex2 rev121_s0_ur
    rev121_vertex3_mem rev121_vertex2_mem (by decide)
theorem rev121_slab0 (p : Point) (hp : p∈IntegerCarrier rev121_planes)
    (hx0 : rev121_s0_ll.real.1≤p.1) (hx1 : p.1≤rev121_s0_lr.real.1) :
    p∈rationalHull (fractionRow121.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev121_plane67 rev121_plane16 rev121_s0_ll rev121_s0_lr rev121_s0_ul rev121_s0_ur
    (by decide) rev121_s0_ll_mem rev121_s0_lr_mem rev121_s0_ul_mem rev121_s0_ur_mem p
    (hp _ rev121_plane67_mem) (hp _ rev121_plane16_mem) hx0 hx1
def rev121_s1_ll : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev121_s1_ll_mem : rev121_s1_ll.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane49 rev121_vertex0 rev121_vertex1 rev121_s1_ll
    rev121_vertex0_mem rev121_vertex1_mem (by decide)
def rev121_s1_lr : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev121_s1_lr_mem : rev121_s1_lr.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane49 rev121_vertex0 rev121_vertex1 rev121_s1_lr
    rev121_vertex0_mem rev121_vertex1_mem (by decide)
def rev121_s1_ul : FractionPoint := ⟨49200521405821067,212798949946400000,190398871400374124151697,247614986147130504000000⟩
theorem rev121_s1_ul_mem : rev121_s1_ul.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane16 rev121_vertex3 rev121_vertex2 rev121_s1_ul
    rev121_vertex3_mem rev121_vertex2_mem (by decide)
def rev121_s1_ur : FractionPoint := ⟨103496514973,446179000000,638671578398765351,830685353904000000⟩
theorem rev121_s1_ur_mem : rev121_s1_ur.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane16 rev121_vertex3 rev121_vertex2 rev121_s1_ur
    rev121_vertex3_mem rev121_vertex2_mem (by decide)
theorem rev121_slab1 (p : Point) (hp : p∈IntegerCarrier rev121_planes)
    (hx0 : rev121_s1_ll.real.1≤p.1) (hx1 : p.1≤rev121_s1_lr.real.1) :
    p∈rationalHull (fractionRow121.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev121_plane49 rev121_plane16 rev121_s1_ll rev121_s1_lr rev121_s1_ul rev121_s1_ur
    (by decide) rev121_s1_ll_mem rev121_s1_lr_mem rev121_s1_ul_mem rev121_s1_ur_mem p
    (hp _ rev121_plane49_mem) (hp _ rev121_plane16_mem) hx0 hx1
def rev121_s2_ll : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev121_s2_ll_mem : rev121_s2_ll.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane34 rev121_vertex1 rev121_vertex2 rev121_s2_ll
    rev121_vertex1_mem rev121_vertex2_mem (by decide)
def rev121_s2_lr : FractionPoint := ⟨247349711339380133,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev121_s2_lr_mem : rev121_s2_lr.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane34 rev121_vertex1 rev121_vertex2 rev121_s2_lr
    rev121_vertex1_mem rev121_vertex2_mem (by decide)
def rev121_s2_ul : FractionPoint := ⟨103496514973,446179000000,638671578398765351,830685353904000000⟩
theorem rev121_s2_ul_mem : rev121_s2_ul.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane16 rev121_vertex3 rev121_vertex2 rev121_s2_ul
    rev121_vertex3_mem rev121_vertex2_mem (by decide)
def rev121_s2_ur : FractionPoint := ⟨247349711339380133,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev121_s2_ur_mem : rev121_s2_ur.real ∈ rationalHull (fractionRow121.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow121 rev121_plane16 rev121_vertex3 rev121_vertex2 rev121_s2_ur
    rev121_vertex3_mem rev121_vertex2_mem (by decide)
theorem rev121_slab2 (p : Point) (hp : p∈IntegerCarrier rev121_planes)
    (hx0 : rev121_s2_ll.real.1≤p.1) (hx1 : p.1≤rev121_s2_lr.real.1) :
    p∈rationalHull (fractionRow121.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev121_plane34 rev121_plane16 rev121_s2_ll rev121_s2_lr rev121_s2_ul rev121_s2_ur
    (by decide) rev121_s2_ll_mem rev121_s2_lr_mem rev121_s2_ul_mem rev121_s2_ur_mem p
    (hp _ rev121_plane34_mem) (hp _ rev121_plane16_mem) hx0 hx1
theorem rev121_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev121_planes) : rev121_s0_ll.real.1≤p.1 := by
  have hc := rev121_plane16.combine_sound rev121_plane67 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev121_plane16_mem) (hp _ rev121_plane67_mem)
  exact (rev121_plane16.combine rev121_plane67 202532000000 1861776000000).xBoundCheck_sound rev121_s0_ll.nx rev121_s0_ll.dx true (by decide) p hc
theorem rev121_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev121_planes) : p.1≤rev121_s2_lr.real.1 := by
  have hc := rev121_plane16.combine_sound rev121_plane34 1440116000000 1861776000000 (by decide) (by decide) p
    (hp _ rev121_plane16_mem) (hp _ rev121_plane34_mem)
  exact (rev121_plane16.combine rev121_plane34 1440116000000 1861776000000).xBoundCheck_sound rev121_s2_lr.nx rev121_s2_lr.dx false (by decide) p hc
theorem rev121_hull (p : Point) (hp : p∈IntegerCarrier rev121_planes) :
    p∈rationalHull (fractionRow121.map FractionPoint.rational) := by
  have hxlo := rev121_bound0_lo p hp
  have hxhi := rev121_bound0_hi p hp
  by_cases h0 : p.1≤rev121_s0_lr.real.1
  · exact rev121_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev121_s1_lr.real.1
  · exact rev121_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev121_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull121 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,0,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow121 := by
  rw [← fractionRow121_correct]
  exact rev121_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull121
