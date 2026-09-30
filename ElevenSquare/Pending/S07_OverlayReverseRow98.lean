import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev98_planes : List IntegerPlane := integerOverlayPlanes ![7,0,15,8]
def rev98_plane7 : IntegerPlane := ⟨(-202532000000),(-1861776000000),(-585903739447)⟩
theorem rev98_plane7_mem : rev98_plane7 ∈ rev98_planes := by decide
def rev98_plane29 : IntegerPlane := ⟨(-2129316000000),1440116000000,(-1301343880216)⟩
theorem rev98_plane29_mem : rev98_plane29 ∈ rev98_planes := by decide
def rev98_plane54 : IntegerPlane := ⟨(-1440116000000),2129316000000,(-612143880216)⟩
theorem rev98_plane54_mem : rev98_plane54 ∈ rev98_planes := by decide
def rev98_plane76 : IntegerPlane := ⟨1861776000000,202532000000,1478404260553⟩
theorem rev98_plane76_mem : rev98_plane76 ∈ rev98_planes := by decide
def rev98_vertex0 : FractionPoint := fractionRow98[0]!
theorem rev98_vertex0_mem : rev98_vertex0∈fractionRow98 := by decide
def rev98_vertex1 : FractionPoint := fractionRow98[1]!
theorem rev98_vertex1_mem : rev98_vertex1∈fractionRow98 := by decide
def rev98_vertex2 : FractionPoint := fractionRow98[2]!
theorem rev98_vertex2_mem : rev98_vertex2∈fractionRow98 := by decide
def rev98_vertex3 : FractionPoint := fractionRow98[3]!
theorem rev98_vertex3_mem : rev98_vertex3∈fractionRow98 := by decide
def rev98_s0_ll : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev98_s0_ll_mem : rev98_s0_ll.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane7 rev98_vertex2 rev98_vertex3 rev98_s0_ll
    rev98_vertex2_mem rev98_vertex3_mem (by decide)
def rev98_s0_lr : FractionPoint := ⟨342682485027,446179000000,192013775505234649,830685353904000000⟩
theorem rev98_s0_lr_mem : rev98_s0_lr.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane7 rev98_vertex2 rev98_vertex3 rev98_s0_lr
    rev98_vertex2_mem rev98_vertex3_mem (by decide)
def rev98_s0_ul : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev98_s0_ul_mem : rev98_s0_ul.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane29 rev98_vertex2 rev98_vertex1 rev98_s0_ul
    rev98_vertex2_mem rev98_vertex1_mem (by decide)
def rev98_s0_ur : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev98_s0_ur_mem : rev98_s0_ur.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane29 rev98_vertex2 rev98_vertex1 rev98_s0_ur
    rev98_vertex2_mem rev98_vertex1_mem (by decide)
theorem rev98_slab0 (p : Point) (hp : p∈IntegerCarrier rev98_planes)
    (hx0 : rev98_s0_ll.real.1≤p.1) (hx1 : p.1≤rev98_s0_lr.real.1) :
    p∈rationalHull (fractionRow98.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev98_plane7 rev98_plane29 rev98_s0_ll rev98_s0_lr rev98_s0_ul rev98_s0_ur
    (by decide) rev98_s0_ll_mem rev98_s0_lr_mem rev98_s0_ul_mem rev98_s0_ur_mem p
    (hp _ rev98_plane7_mem) (hp _ rev98_plane29_mem) hx0 hx1
def rev98_s1_ll : FractionPoint := ⟨342682485027,446179000000,192013775505234649,830685353904000000⟩
theorem rev98_s1_ll_mem : rev98_s1_ll.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane7 rev98_vertex2 rev98_vertex3 rev98_s1_ll
    rev98_vertex2_mem rev98_vertex3_mem (by decide)
def rev98_s1_lr : FractionPoint := ⟨163598428540578933,212798949946400000,57216114746756379848303,247614986147130504000000⟩
theorem rev98_s1_lr_mem : rev98_s1_lr.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane7 rev98_vertex2 rev98_vertex3 rev98_s1_lr
    rev98_vertex2_mem rev98_vertex3_mem (by decide)
def rev98_s1_ul : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev98_s1_ul_mem : rev98_s1_ul.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane54 rev98_vertex1 rev98_vertex0 rev98_s1_ul
    rev98_vertex1_mem rev98_vertex0_mem (by decide)
def rev98_s1_ur : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev98_s1_ur_mem : rev98_s1_ur.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane54 rev98_vertex1 rev98_vertex0 rev98_s1_ur
    rev98_vertex1_mem rev98_vertex0_mem (by decide)
theorem rev98_slab1 (p : Point) (hp : p∈IntegerCarrier rev98_planes)
    (hx0 : rev98_s1_ll.real.1≤p.1) (hx1 : p.1≤rev98_s1_lr.real.1) :
    p∈rationalHull (fractionRow98.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev98_plane7 rev98_plane54 rev98_s1_ll rev98_s1_lr rev98_s1_ul rev98_s1_ur
    (by decide) rev98_s1_ll_mem rev98_s1_lr_mem rev98_s1_ul_mem rev98_s1_ur_mem p
    (hp _ rev98_plane7_mem) (hp _ rev98_plane54_mem) hx0 hx1
def rev98_s2_ll : FractionPoint := ⟨163598428540578933,212798949946400000,57216114746756379848303,247614986147130504000000⟩
theorem rev98_s2_ll_mem : rev98_s2_ll.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane7 rev98_vertex2 rev98_vertex3 rev98_s2_ll
    rev98_vertex2_mem rev98_vertex3_mem (by decide)
def rev98_s2_lr : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev98_s2_lr_mem : rev98_s2_lr.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane7 rev98_vertex2 rev98_vertex3 rev98_s2_lr
    rev98_vertex2_mem rev98_vertex3_mem (by decide)
def rev98_s2_ul : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev98_s2_ul_mem : rev98_s2_ul.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane76 rev98_vertex0 rev98_vertex3 rev98_s2_ul
    rev98_vertex0_mem rev98_vertex3_mem (by decide)
def rev98_s2_ur : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev98_s2_ur_mem : rev98_s2_ur.real ∈ rationalHull (fractionRow98.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow98 rev98_plane76 rev98_vertex0 rev98_vertex3 rev98_s2_ur
    rev98_vertex0_mem rev98_vertex3_mem (by decide)
theorem rev98_slab2 (p : Point) (hp : p∈IntegerCarrier rev98_planes)
    (hx0 : rev98_s2_ll.real.1≤p.1) (hx1 : p.1≤rev98_s2_lr.real.1) :
    p∈rationalHull (fractionRow98.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev98_plane7 rev98_plane76 rev98_s2_ll rev98_s2_lr rev98_s2_ul rev98_s2_ur
    (by decide) rev98_s2_ll_mem rev98_s2_lr_mem rev98_s2_ul_mem rev98_s2_ur_mem p
    (hp _ rev98_plane7_mem) (hp _ rev98_plane76_mem) hx0 hx1
theorem rev98_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev98_planes) : rev98_s0_ll.real.1≤p.1 := by
  have hc := rev98_plane7.combine_sound rev98_plane29 1440116000000 1861776000000 (by decide) (by decide) p
    (hp _ rev98_plane7_mem) (hp _ rev98_plane29_mem)
  exact (rev98_plane7.combine rev98_plane29 1440116000000 1861776000000).xBoundCheck_sound rev98_s0_ll.nx rev98_s0_ll.dx true (by decide) p hc
theorem rev98_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev98_planes) : p.1≤rev98_s2_lr.real.1 := by
  have hc := rev98_plane7.combine_sound rev98_plane76 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev98_plane7_mem) (hp _ rev98_plane76_mem)
  exact (rev98_plane7.combine rev98_plane76 202532000000 1861776000000).xBoundCheck_sound rev98_s2_lr.nx rev98_s2_lr.dx false (by decide) p hc
theorem rev98_hull (p : Point) (hp : p∈IntegerCarrier rev98_planes) :
    p∈rationalHull (fractionRow98.map FractionPoint.rational) := by
  have hxlo := rev98_bound0_lo p hp
  have hxhi := rev98_bound0_hi p hp
  by_cases h0 : p.1≤rev98_s0_lr.real.1
  · exact rev98_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev98_s1_lr.real.1
  · exact rev98_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev98_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull98 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow98 := by
  rw [← fractionRow98_correct]
  exact rev98_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull98
