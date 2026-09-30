import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev193_planes : List IntegerPlane := integerOverlayPlanes ![13,10,9,6]
def rev193_plane13 : IntegerPlane := ⟨(-13084000000),(-2218132000000),(-1607629024972)⟩
theorem rev193_plane13_mem : rev193_plane13 ∈ rev193_planes := by decide
def rev193_plane14 : IntegerPlane := ⟨2099728000000,(-1393416000000),(-33871860516)⟩
theorem rev193_plane14_mem : rev193_plane14 ∈ rev193_planes := by decide
def rev193_plane48 : IntegerPlane := ⟨(-1468788000000),2093220000000,880675273104⟩
theorem rev193_plane48_mem : rev193_plane48 ∈ rev193_planes := by decide
def rev193_plane49 : IntegerPlane := ⟨(-2168356000000),(-51300000000),(-1004834835544)⟩
theorem rev193_plane49_mem : rev193_plane49 ∈ rev193_planes := by decide
def rev193_vertex0 : FractionPoint := fractionRow193[0]!
theorem rev193_vertex0_mem : rev193_vertex0∈fractionRow193 := by decide
def rev193_vertex1 : FractionPoint := fractionRow193[1]!
theorem rev193_vertex1_mem : rev193_vertex1∈fractionRow193 := by decide
def rev193_vertex2 : FractionPoint := fractionRow193[2]!
theorem rev193_vertex2_mem : rev193_vertex2∈fractionRow193 := by decide
def rev193_vertex3 : FractionPoint := fractionRow193[3]!
theorem rev193_vertex3_mem : rev193_vertex3∈fractionRow193 := by decide
def rev193_s0_ll : FractionPoint := ⟨3270661284241,7332499000000,80699534251423,109987485000000⟩
theorem rev193_s0_ll_mem : rev193_s0_ll.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane49 rev193_vertex3 rev193_vertex0 rev193_s0_ll
    rev193_vertex3_mem rev193_vertex0_mem (by decide)
def rev193_s0_lr : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev193_s0_lr_mem : rev193_s0_lr.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane49 rev193_vertex3 rev193_vertex0 rev193_s0_lr
    rev193_vertex3_mem rev193_vertex0_mem (by decide)
def rev193_s0_ul : FractionPoint := ⟨3270661284241,7332499000000,80699534251423,109987485000000⟩
theorem rev193_s0_ul_mem : rev193_s0_ul.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane48 rev193_vertex3 rev193_vertex2 rev193_s0_ul
    rev193_vertex3_mem rev193_vertex2_mem (by decide)
def rev193_s0_ur : FractionPoint := ⟨7060476758071777,15819173098000000,2025158177074610746039,2759417459349630000000⟩
theorem rev193_s0_ur_mem : rev193_s0_ur.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane48 rev193_vertex3 rev193_vertex2 rev193_s0_ur
    rev193_vertex3_mem rev193_vertex2_mem (by decide)
theorem rev193_slab0 (p : Point) (hp : p∈IntegerCarrier rev193_planes)
    (hx0 : rev193_s0_ll.real.1≤p.1) (hx1 : p.1≤rev193_s0_lr.real.1) :
    p∈rationalHull (fractionRow193.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev193_plane49 rev193_plane48 rev193_s0_ll rev193_s0_lr rev193_s0_ul rev193_s0_ur
    (by decide) rev193_s0_ll_mem rev193_s0_lr_mem rev193_s0_ul_mem rev193_s0_ur_mem p
    (hp _ rev193_plane49_mem) (hp _ rev193_plane48_mem) hx0 hx1
def rev193_s1_ll : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev193_s1_ll_mem : rev193_s1_ll.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane13 rev193_vertex0 rev193_vertex1 rev193_s1_ll
    rev193_vertex0_mem rev193_vertex1_mem (by decide)
def rev193_s1_lr : FractionPoint := ⟨27062046846878853,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev193_s1_lr_mem : rev193_s1_lr.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane13 rev193_vertex0 rev193_vertex1 rev193_s1_lr
    rev193_vertex0_mem rev193_vertex1_mem (by decide)
def rev193_s1_ul : FractionPoint := ⟨7060476758071777,15819173098000000,2025158177074610746039,2759417459349630000000⟩
theorem rev193_s1_ul_mem : rev193_s1_ul.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane48 rev193_vertex3 rev193_vertex2 rev193_s1_ul
    rev193_vertex3_mem rev193_vertex2_mem (by decide)
def rev193_s1_ur : FractionPoint := ⟨27062046846878853,58446316538000000,7601719620263289877843,10195083225306030000000⟩
theorem rev193_s1_ur_mem : rev193_s1_ur.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane48 rev193_vertex3 rev193_vertex2 rev193_s1_ur
    rev193_vertex3_mem rev193_vertex2_mem (by decide)
theorem rev193_slab1 (p : Point) (hp : p∈IntegerCarrier rev193_planes)
    (hx0 : rev193_s1_ll.real.1≤p.1) (hx1 : p.1≤rev193_s1_lr.real.1) :
    p∈rationalHull (fractionRow193.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev193_plane13 rev193_plane48 rev193_s1_ll rev193_s1_lr rev193_s1_ul rev193_s1_ur
    (by decide) rev193_s1_ll_mem rev193_s1_lr_mem rev193_s1_ul_mem rev193_s1_ur_mem p
    (hp _ rev193_plane13_mem) (hp _ rev193_plane48_mem) hx0 hx1
def rev193_s2_ll : FractionPoint := ⟨27062046846878853,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev193_s2_ll_mem : rev193_s2_ll.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane14 rev193_vertex1 rev193_vertex2 rev193_s2_ll
    rev193_vertex1_mem rev193_vertex2_mem (by decide)
def rev193_s2_lr : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev193_s2_lr_mem : rev193_s2_lr.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane14 rev193_vertex1 rev193_vertex2 rev193_s2_lr
    rev193_vertex1_mem rev193_vertex2_mem (by decide)
def rev193_s2_ul : FractionPoint := ⟨27062046846878853,58446316538000000,7601719620263289877843,10195083225306030000000⟩
theorem rev193_s2_ul_mem : rev193_s2_ul.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane48 rev193_vertex3 rev193_vertex2 rev193_s2_ul
    rev193_vertex3_mem rev193_vertex2_mem (by decide)
def rev193_s2_ur : FractionPoint := ⟨8029484447765151,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev193_s2_ur_mem : rev193_s2_ur.real ∈ rationalHull (fractionRow193.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow193 rev193_plane48 rev193_vertex3 rev193_vertex2 rev193_s2_ur
    rev193_vertex3_mem rev193_vertex2_mem (by decide)
theorem rev193_slab2 (p : Point) (hp : p∈IntegerCarrier rev193_planes)
    (hx0 : rev193_s2_ll.real.1≤p.1) (hx1 : p.1≤rev193_s2_lr.real.1) :
    p∈rationalHull (fractionRow193.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev193_plane14 rev193_plane48 rev193_s2_ll rev193_s2_lr rev193_s2_ul rev193_s2_ur
    (by decide) rev193_s2_ll_mem rev193_s2_lr_mem rev193_s2_ul_mem rev193_s2_ur_mem p
    (hp _ rev193_plane14_mem) (hp _ rev193_plane48_mem) hx0 hx1
theorem rev193_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev193_planes) : rev193_s0_ll.real.1≤p.1 := by
  have hc := rev193_plane48.combine_sound rev193_plane49 51300000000 2093220000000 (by decide) (by decide) p
    (hp _ rev193_plane48_mem) (hp _ rev193_plane49_mem)
  exact (rev193_plane48.combine rev193_plane49 51300000000 2093220000000).xBoundCheck_sound rev193_s0_ll.nx rev193_s0_ll.dx true (by decide) p hc
theorem rev193_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev193_planes) : p.1≤rev193_s2_lr.real.1 := by
  have hc := rev193_plane14.combine_sound rev193_plane48 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev193_plane14_mem) (hp _ rev193_plane48_mem)
  exact (rev193_plane14.combine rev193_plane48 2093220000000 1393416000000).xBoundCheck_sound rev193_s2_lr.nx rev193_s2_lr.dx false (by decide) p hc
theorem rev193_hull (p : Point) (hp : p∈IntegerCarrier rev193_planes) :
    p∈rationalHull (fractionRow193.map FractionPoint.rational) := by
  have hxlo := rev193_bound0_lo p hp
  have hxhi := rev193_bound0_hi p hp
  by_cases h0 : p.1≤rev193_s0_lr.real.1
  · exact rev193_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev193_s1_lr.real.1
  · exact rev193_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev193_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull193 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow193 := by
  rw [← fractionRow193_correct]
  exact rev193_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull193
