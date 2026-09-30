import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev110_planes : List IntegerPlane := integerOverlayPlanes ![8,10,0,7]
def rev110_plane16 : IntegerPlane := ⟨202532000000,1861776000000,1478404260553⟩
theorem rev110_plane16_mem : rev110_plane16 ∈ rev110_planes := by decide
def rev110_plane39 : IntegerPlane := ⟨(-2129316000000),1440116000000,612143880216⟩
theorem rev110_plane39_mem : rev110_plane39 ∈ rev110_planes := by decide
def rev110_plane49 : IntegerPlane := ⟨1440116000000,(-2129316000000),(-1301343880216)⟩
theorem rev110_plane49_mem : rev110_plane49 ∈ rev110_planes := by decide
def rev110_vertex0 : FractionPoint := fractionRow110[0]!
theorem rev110_vertex0_mem : rev110_vertex0∈fractionRow110 := by decide
def rev110_vertex1 : FractionPoint := fractionRow110[1]!
theorem rev110_vertex1_mem : rev110_vertex1∈fractionRow110 := by decide
def rev110_vertex2 : FractionPoint := fractionRow110[2]!
theorem rev110_vertex2_mem : rev110_vertex2∈fractionRow110 := by decide
def rev110_s0_ll : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev110_s0_ll_mem : rev110_s0_ll.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane49 rev110_vertex2 rev110_vertex0 rev110_s0_ll
    rev110_vertex2_mem rev110_vertex0_mem (by decide)
def rev110_s0_lr : FractionPoint := ⟨247349711339380133,1063994749732000000,87041766652045773285877,113279052226017165600000⟩
theorem rev110_s0_lr_mem : rev110_s0_lr.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane49 rev110_vertex2 rev110_vertex0 rev110_s0_lr
    rev110_vertex2_mem rev110_vertex0_mem (by decide)
def rev110_s0_ul : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev110_s0_ul_mem : rev110_s0_ul.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane39 rev110_vertex2 rev110_vertex1 rev110_s0_ul
    rev110_vertex2_mem rev110_vertex1_mem (by decide)
def rev110_s0_ur : FractionPoint := ⟨247349711339380133,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev110_s0_ur_mem : rev110_s0_ur.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane39 rev110_vertex2 rev110_vertex1 rev110_s0_ur
    rev110_vertex2_mem rev110_vertex1_mem (by decide)
theorem rev110_slab0 (p : Point) (hp : p∈IntegerCarrier rev110_planes)
    (hx0 : rev110_s0_ll.real.1≤p.1) (hx1 : p.1≤rev110_s0_lr.real.1) :
    p∈rationalHull (fractionRow110.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev110_plane49 rev110_plane39 rev110_s0_ll rev110_s0_lr rev110_s0_ul rev110_s0_ur
    (by decide) rev110_s0_ll_mem rev110_s0_lr_mem rev110_s0_ul_mem rev110_s0_ur_mem p
    (hp _ rev110_plane49_mem) (hp _ rev110_plane39_mem) hx0 hx1
def rev110_s1_ll : FractionPoint := ⟨247349711339380133,1063994749732000000,87041766652045773285877,113279052226017165600000⟩
theorem rev110_s1_ll_mem : rev110_s1_ll.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane49 rev110_vertex2 rev110_vertex0 rev110_s1_ll
    rev110_vertex2_mem rev110_vertex0_mem (by decide)
def rev110_s1_lr : FractionPoint := ⟨8633083839650573,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev110_s1_lr_mem : rev110_s1_lr.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane49 rev110_vertex2 rev110_vertex0 rev110_s1_lr
    rev110_vertex2_mem rev110_vertex0_mem (by decide)
def rev110_s1_ul : FractionPoint := ⟨247349711339380133,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev110_s1_ul_mem : rev110_s1_ul.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane16 rev110_vertex1 rev110_vertex0 rev110_s1_ul
    rev110_vertex1_mem rev110_vertex0_mem (by decide)
def rev110_s1_ur : FractionPoint := ⟨8633083839650573,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev110_s1_ur_mem : rev110_s1_ur.real ∈ rationalHull (fractionRow110.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow110 rev110_plane16 rev110_vertex1 rev110_vertex0 rev110_s1_ur
    rev110_vertex1_mem rev110_vertex0_mem (by decide)
theorem rev110_slab1 (p : Point) (hp : p∈IntegerCarrier rev110_planes)
    (hx0 : rev110_s1_ll.real.1≤p.1) (hx1 : p.1≤rev110_s1_lr.real.1) :
    p∈rationalHull (fractionRow110.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev110_plane49 rev110_plane16 rev110_s1_ll rev110_s1_lr rev110_s1_ul rev110_s1_ur
    (by decide) rev110_s1_ll_mem rev110_s1_lr_mem rev110_s1_ul_mem rev110_s1_ur_mem p
    (hp _ rev110_plane49_mem) (hp _ rev110_plane16_mem) hx0 hx1
theorem rev110_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev110_planes) : rev110_s0_ll.real.1≤p.1 := by
  have hc := rev110_plane39.combine_sound rev110_plane49 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev110_plane39_mem) (hp _ rev110_plane49_mem)
  exact (rev110_plane39.combine rev110_plane49 2129316000000 1440116000000).xBoundCheck_sound rev110_s0_ll.nx rev110_s0_ll.dx true (by decide) p hc
theorem rev110_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev110_planes) : p.1≤rev110_s1_lr.real.1 := by
  have hc := rev110_plane16.combine_sound rev110_plane49 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev110_plane16_mem) (hp _ rev110_plane49_mem)
  exact (rev110_plane16.combine rev110_plane49 2129316000000 1861776000000).xBoundCheck_sound rev110_s1_lr.nx rev110_s1_lr.dx false (by decide) p hc
theorem rev110_hull (p : Point) (hp : p∈IntegerCarrier rev110_planes) :
    p∈rationalHull (fractionRow110.map FractionPoint.rational) := by
  have hxlo := rev110_bound0_lo p hp
  have hxhi := rev110_bound0_hi p hp
  by_cases h0 : p.1≤rev110_s0_lr.real.1
  · exact rev110_slab0 p hp hxlo h0
  exact rev110_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull110 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,10,0,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow110 := by
  rw [← fractionRow110_correct]
  exact rev110_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull110
