import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev11_planes : List IntegerPlane := integerOverlayPlanes ![0,7,7,5]
def rev11_plane9 : IntegerPlane := ⟨2129316000000,1440116000000,827972119784⟩
theorem rev11_plane9_mem : rev11_plane9 ∈ rev11_planes := by decide
def rev11_plane47 : IntegerPlane := ⟨(-1861776000000),202532000000,(-383371739447)⟩
theorem rev11_plane47_mem : rev11_plane47 ∈ rev11_planes := by decide
def rev11_plane64 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-827972119784)⟩
theorem rev11_plane64_mem : rev11_plane64 ∈ rev11_planes := by decide
def rev11_vertex0 : FractionPoint := fractionRow11[0]!
theorem rev11_vertex0_mem : rev11_vertex0∈fractionRow11 := by decide
def rev11_vertex1 : FractionPoint := fractionRow11[1]!
theorem rev11_vertex1_mem : rev11_vertex1∈fractionRow11 := by decide
def rev11_vertex2 : FractionPoint := fractionRow11[2]!
theorem rev11_vertex2_mem : rev11_vertex2∈fractionRow11 := by decide
def rev11_s0_ll : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev11_s0_ll_mem : rev11_s0_ll.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane64 rev11_vertex2 rev11_vertex0 rev11_s0_ll
    rev11_vertex2_mem rev11_vertex0_mem (by decide)
def rev11_s0_lr : FractionPoint := ⟨35989531264477447,155621401706400000,96276352560163999669457,414208925744831028000000⟩
theorem rev11_s0_lr_mem : rev11_s0_lr.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane64 rev11_vertex2 rev11_vertex0 rev11_s0_lr
    rev11_vertex2_mem rev11_vertex0_mem (by decide)
def rev11_s0_ul : FractionPoint := ⟨49200521405821067,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev11_s0_ul_mem : rev11_s0_ul.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane47 rev11_vertex2 rev11_vertex1 rev11_s0_ul
    rev11_vertex2_mem rev11_vertex1_mem (by decide)
def rev11_s0_ur : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev11_s0_ur_mem : rev11_s0_ur.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane47 rev11_vertex2 rev11_vertex1 rev11_s0_ur
    rev11_vertex2_mem rev11_vertex1_mem (by decide)
theorem rev11_slab0 (p : Point) (hp : p∈IntegerCarrier rev11_planes)
    (hx0 : rev11_s0_ll.real.1≤p.1) (hx1 : p.1≤rev11_s0_lr.real.1) :
    p∈rationalHull (fractionRow11.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev11_plane64 rev11_plane47 rev11_s0_ll rev11_s0_lr rev11_s0_ul rev11_s0_ur
    (by decide) rev11_s0_ll_mem rev11_s0_lr_mem rev11_s0_ul_mem rev11_s0_ur_mem p
    (hp _ rev11_plane64_mem) (hp _ rev11_plane47_mem) hx0 hx1
def rev11_s1_ll : FractionPoint := ⟨35989531264477447,155621401706400000,96276352560163999669457,414208925744831028000000⟩
theorem rev11_s1_ll_mem : rev11_s1_ll.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane64 rev11_vertex2 rev11_vertex0 rev11_s1_ll
    rev11_vertex2_mem rev11_vertex0_mem (by decide)
def rev11_s1_lr : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev11_s1_lr_mem : rev11_s1_lr.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane64 rev11_vertex2 rev11_vertex0 rev11_s1_lr
    rev11_vertex2_mem rev11_vertex0_mem (by decide)
def rev11_s1_ul : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev11_s1_ul_mem : rev11_s1_ul.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane9 rev11_vertex1 rev11_vertex0 rev11_s1_ul
    rev11_vertex1_mem rev11_vertex0_mem (by decide)
def rev11_s1_ur : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev11_s1_ur_mem : rev11_s1_ur.real ∈ rationalHull (fractionRow11.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow11 rev11_plane9 rev11_vertex1 rev11_vertex0 rev11_s1_ur
    rev11_vertex1_mem rev11_vertex0_mem (by decide)
theorem rev11_slab1 (p : Point) (hp : p∈IntegerCarrier rev11_planes)
    (hx0 : rev11_s1_ll.real.1≤p.1) (hx1 : p.1≤rev11_s1_lr.real.1) :
    p∈rationalHull (fractionRow11.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev11_plane64 rev11_plane9 rev11_s1_ll rev11_s1_lr rev11_s1_ul rev11_s1_ur
    (by decide) rev11_s1_ll_mem rev11_s1_lr_mem rev11_s1_ul_mem rev11_s1_ur_mem p
    (hp _ rev11_plane64_mem) (hp _ rev11_plane9_mem) hx0 hx1
theorem rev11_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev11_planes) : rev11_s0_ll.real.1≤p.1 := by
  have hc := rev11_plane47.combine_sound rev11_plane64 2129316000000 202532000000 (by decide) (by decide) p
    (hp _ rev11_plane47_mem) (hp _ rev11_plane64_mem)
  exact (rev11_plane47.combine rev11_plane64 2129316000000 202532000000).xBoundCheck_sound rev11_s0_ll.nx rev11_s0_ll.dx true (by decide) p hc
theorem rev11_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev11_planes) : p.1≤rev11_s1_lr.real.1 := by
  have hc := rev11_plane9.combine_sound rev11_plane64 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev11_plane9_mem) (hp _ rev11_plane64_mem)
  exact (rev11_plane9.combine rev11_plane64 2129316000000 1440116000000).xBoundCheck_sound rev11_s1_lr.nx rev11_s1_lr.dx false (by decide) p hc
theorem rev11_hull (p : Point) (hp : p∈IntegerCarrier rev11_planes) :
    p∈rationalHull (fractionRow11.map FractionPoint.rational) := by
  have hxlo := rev11_bound0_lo p hp
  have hxhi := rev11_bound0_hi p hp
  by_cases h0 : p.1≤rev11_s0_lr.real.1
  · exact rev11_slab0 p hp hxlo h0
  exact rev11_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull11 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,7,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow11 := by
  rw [← fractionRow11_correct]
  exact rev11_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull11
