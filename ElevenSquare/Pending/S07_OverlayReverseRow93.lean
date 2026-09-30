import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev93_planes : List IntegerPlane := integerOverlayPlanes ![7,0,10,8]
def rev93_plane29 : IntegerPlane := ⟨(-2129316000000),1440116000000,(-1301343880216)⟩
theorem rev93_plane29_mem : rev93_plane29 ∈ rev93_planes := by decide
def rev93_plane59 : IntegerPlane := ⟨1440116000000,(-2129316000000),612143880216⟩
theorem rev93_plane59_mem : rev93_plane59 ∈ rev93_planes := by decide
def rev93_plane76 : IntegerPlane := ⟨1861776000000,202532000000,1478404260553⟩
theorem rev93_plane76_mem : rev93_plane76 ∈ rev93_planes := by decide
def rev93_vertex0 : FractionPoint := fractionRow93[0]!
theorem rev93_vertex0_mem : rev93_vertex0∈fractionRow93 := by decide
def rev93_vertex1 : FractionPoint := fractionRow93[1]!
theorem rev93_vertex1_mem : rev93_vertex1∈fractionRow93 := by decide
def rev93_vertex2 : FractionPoint := fractionRow93[2]!
theorem rev93_vertex2_mem : rev93_vertex2∈fractionRow93 := by decide
def rev93_s0_ll : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev93_s0_ll_mem : rev93_s0_ll.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane59 rev93_vertex1 rev93_vertex2 rev93_s0_ll
    rev93_vertex1_mem rev93_vertex2_mem (by decide)
def rev93_s0_lr : FractionPoint := ⟨119631870441922553,155621401706400000,96276352560163999669457,414208925744831028000000⟩
theorem rev93_s0_lr_mem : rev93_s0_lr.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane59 rev93_vertex1 rev93_vertex2 rev93_s0_lr
    rev93_vertex1_mem rev93_vertex2_mem (by decide)
def rev93_s0_ul : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev93_s0_ul_mem : rev93_s0_ul.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane29 rev93_vertex1 rev93_vertex0 rev93_s0_ul
    rev93_vertex1_mem rev93_vertex0_mem (by decide)
def rev93_s0_ur : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev93_s0_ur_mem : rev93_s0_ur.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane29 rev93_vertex1 rev93_vertex0 rev93_s0_ur
    rev93_vertex1_mem rev93_vertex0_mem (by decide)
theorem rev93_slab0 (p : Point) (hp : p∈IntegerCarrier rev93_planes)
    (hx0 : rev93_s0_ll.real.1≤p.1) (hx1 : p.1≤rev93_s0_lr.real.1) :
    p∈rationalHull (fractionRow93.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev93_plane59 rev93_plane29 rev93_s0_ll rev93_s0_lr rev93_s0_ul rev93_s0_ur
    (by decide) rev93_s0_ll_mem rev93_s0_lr_mem rev93_s0_ul_mem rev93_s0_ur_mem p
    (hp _ rev93_plane59_mem) (hp _ rev93_plane29_mem) hx0 hx1
def rev93_s1_ll : FractionPoint := ⟨119631870441922553,155621401706400000,96276352560163999669457,414208925744831028000000⟩
theorem rev93_s1_ll_mem : rev93_s1_ll.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane59 rev93_vertex1 rev93_vertex2 rev93_s1_ll
    rev93_vertex1_mem rev93_vertex2_mem (by decide)
def rev93_s1_lr : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev93_s1_lr_mem : rev93_s1_lr.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane59 rev93_vertex1 rev93_vertex2 rev93_s1_lr
    rev93_vertex1_mem rev93_vertex2_mem (by decide)
def rev93_s1_ul : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev93_s1_ul_mem : rev93_s1_ul.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane76 rev93_vertex0 rev93_vertex2 rev93_s1_ul
    rev93_vertex0_mem rev93_vertex2_mem (by decide)
def rev93_s1_ur : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev93_s1_ur_mem : rev93_s1_ur.real ∈ rationalHull (fractionRow93.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow93 rev93_plane76 rev93_vertex0 rev93_vertex2 rev93_s1_ur
    rev93_vertex0_mem rev93_vertex2_mem (by decide)
theorem rev93_slab1 (p : Point) (hp : p∈IntegerCarrier rev93_planes)
    (hx0 : rev93_s1_ll.real.1≤p.1) (hx1 : p.1≤rev93_s1_lr.real.1) :
    p∈rationalHull (fractionRow93.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev93_plane59 rev93_plane76 rev93_s1_ll rev93_s1_lr rev93_s1_ul rev93_s1_ur
    (by decide) rev93_s1_ll_mem rev93_s1_lr_mem rev93_s1_ul_mem rev93_s1_ur_mem p
    (hp _ rev93_plane59_mem) (hp _ rev93_plane76_mem) hx0 hx1
theorem rev93_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev93_planes) : rev93_s0_ll.real.1≤p.1 := by
  have hc := rev93_plane29.combine_sound rev93_plane59 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev93_plane29_mem) (hp _ rev93_plane59_mem)
  exact (rev93_plane29.combine rev93_plane59 2129316000000 1440116000000).xBoundCheck_sound rev93_s0_ll.nx rev93_s0_ll.dx true (by decide) p hc
theorem rev93_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev93_planes) : p.1≤rev93_s1_lr.real.1 := by
  have hc := rev93_plane59.combine_sound rev93_plane76 202532000000 2129316000000 (by decide) (by decide) p
    (hp _ rev93_plane59_mem) (hp _ rev93_plane76_mem)
  exact (rev93_plane59.combine rev93_plane76 202532000000 2129316000000).xBoundCheck_sound rev93_s1_lr.nx rev93_s1_lr.dx false (by decide) p hc
theorem rev93_hull (p : Point) (hp : p∈IntegerCarrier rev93_planes) :
    p∈rationalHull (fractionRow93.map FractionPoint.rational) := by
  have hxlo := rev93_bound0_lo p hp
  have hxhi := rev93_bound0_hi p hp
  by_cases h0 : p.1≤rev93_s0_lr.real.1
  · exact rev93_slab0 p hp hxlo h0
  exact rev93_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull93 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,10,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow93 := by
  rw [← fractionRow93_correct]
  exact rev93_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull93
