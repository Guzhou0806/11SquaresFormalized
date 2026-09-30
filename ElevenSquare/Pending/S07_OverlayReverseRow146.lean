import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev146_planes : List IntegerPlane := integerOverlayPlanes ![10,8,8,15]
def rev146_plane19 : IntegerPlane := ⟨2129316000000,1440116000000,2741459880216⟩
theorem rev146_plane19_mem : rev146_plane19 ∈ rev146_planes := by decide
def rev146_plane36 : IntegerPlane := ⟨(-202532000000),1861776000000,1275872260553⟩
theorem rev146_plane36_mem : rev146_plane36 ∈ rev146_planes := by decide
def rev146_plane74 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-2741459880216)⟩
theorem rev146_plane74_mem : rev146_plane74 ∈ rev146_planes := by decide
def rev146_vertex0 : FractionPoint := fractionRow146[0]!
theorem rev146_vertex0_mem : rev146_vertex0∈fractionRow146 := by decide
def rev146_vertex1 : FractionPoint := fractionRow146[1]!
theorem rev146_vertex1_mem : rev146_vertex1∈fractionRow146 := by decide
def rev146_vertex2 : FractionPoint := fractionRow146[2]!
theorem rev146_vertex2_mem : rev146_vertex2∈fractionRow146 := by decide
def rev146_s0_ll : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev146_s0_ll_mem : rev146_s0_ll.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane74 rev146_vertex2 rev146_vertex0 rev146_s0_ll
    rev146_vertex2_mem rev146_vertex0_mem (by decide)
def rev146_s0_lr : FractionPoint := ⟨816645038392619867,1063994749732000000,87041766652045773285877,113279052226017165600000⟩
theorem rev146_s0_lr_mem : rev146_s0_lr.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane74 rev146_vertex2 rev146_vertex0 rev146_s0_lr
    rev146_vertex2_mem rev146_vertex0_mem (by decide)
def rev146_s0_ul : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev146_s0_ul_mem : rev146_s0_ul.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane36 rev146_vertex2 rev146_vertex1 rev146_s0_ul
    rev146_vertex2_mem rev146_vertex1_mem (by decide)
def rev146_s0_ur : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev146_s0_ur_mem : rev146_s0_ur.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane36 rev146_vertex2 rev146_vertex1 rev146_s0_ur
    rev146_vertex2_mem rev146_vertex1_mem (by decide)
theorem rev146_slab0 (p : Point) (hp : p∈IntegerCarrier rev146_planes)
    (hx0 : rev146_s0_ll.real.1≤p.1) (hx1 : p.1≤rev146_s0_lr.real.1) :
    p∈rationalHull (fractionRow146.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev146_plane74 rev146_plane36 rev146_s0_ll rev146_s0_lr rev146_s0_ul rev146_s0_ur
    (by decide) rev146_s0_ll_mem rev146_s0_lr_mem rev146_s0_ul_mem rev146_s0_ur_mem p
    (hp _ rev146_plane74_mem) (hp _ rev146_plane36_mem) hx0 hx1
def rev146_s1_ll : FractionPoint := ⟨816645038392619867,1063994749732000000,87041766652045773285877,113279052226017165600000⟩
theorem rev146_s1_ll_mem : rev146_s1_ll.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane74 rev146_vertex2 rev146_vertex0 rev146_s1_ll
    rev146_vertex2_mem rev146_vertex0_mem (by decide)
def rev146_s1_lr : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev146_s1_lr_mem : rev146_s1_lr.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane74 rev146_vertex2 rev146_vertex0 rev146_s1_lr
    rev146_vertex2_mem rev146_vertex0_mem (by decide)
def rev146_s1_ul : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev146_s1_ul_mem : rev146_s1_ul.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane19 rev146_vertex1 rev146_vertex0 rev146_s1_ul
    rev146_vertex1_mem rev146_vertex0_mem (by decide)
def rev146_s1_ur : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev146_s1_ur_mem : rev146_s1_ur.real ∈ rationalHull (fractionRow146.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow146 rev146_plane19 rev146_vertex1 rev146_vertex0 rev146_s1_ur
    rev146_vertex1_mem rev146_vertex0_mem (by decide)
theorem rev146_slab1 (p : Point) (hp : p∈IntegerCarrier rev146_planes)
    (hx0 : rev146_s1_ll.real.1≤p.1) (hx1 : p.1≤rev146_s1_lr.real.1) :
    p∈rationalHull (fractionRow146.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev146_plane74 rev146_plane19 rev146_s1_ll rev146_s1_lr rev146_s1_ul rev146_s1_ur
    (by decide) rev146_s1_ll_mem rev146_s1_lr_mem rev146_s1_ul_mem rev146_s1_ur_mem p
    (hp _ rev146_plane74_mem) (hp _ rev146_plane19_mem) hx0 hx1
theorem rev146_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev146_planes) : rev146_s0_ll.real.1≤p.1 := by
  have hc := rev146_plane36.combine_sound rev146_plane74 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev146_plane36_mem) (hp _ rev146_plane74_mem)
  exact (rev146_plane36.combine rev146_plane74 2129316000000 1861776000000).xBoundCheck_sound rev146_s0_ll.nx rev146_s0_ll.dx true (by decide) p hc
theorem rev146_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev146_planes) : p.1≤rev146_s1_lr.real.1 := by
  have hc := rev146_plane19.combine_sound rev146_plane74 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev146_plane19_mem) (hp _ rev146_plane74_mem)
  exact (rev146_plane19.combine rev146_plane74 2129316000000 1440116000000).xBoundCheck_sound rev146_s1_lr.nx rev146_s1_lr.dx false (by decide) p hc
theorem rev146_hull (p : Point) (hp : p∈IntegerCarrier rev146_planes) :
    p∈rationalHull (fractionRow146.map FractionPoint.rational) := by
  have hxlo := rev146_bound0_lo p hp
  have hxhi := rev146_bound0_hi p hp
  by_cases h0 : p.1≤rev146_s0_lr.real.1
  · exact rev146_slab0 p hp hxlo h0
  exact rev146_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull146 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,8,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow146 := by
  rw [← fractionRow146_correct]
  exact rev146_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull146
