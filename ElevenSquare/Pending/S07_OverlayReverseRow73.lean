import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks9
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev73_planes : List IntegerPlane := integerOverlayPlanes ![5,7,7,0]
def rev73_plane4 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-827972119784)⟩
theorem rev73_plane4_mem : rev73_plane4 ∈ rev73_planes := by decide
def rev73_plane27 : IntegerPlane := ⟨202532000000,(-1861776000000),(-383371739447)⟩
theorem rev73_plane27_mem : rev73_plane27 ∈ rev73_planes := by decide
def rev73_plane69 : IntegerPlane := ⟨1440116000000,2129316000000,827972119784⟩
theorem rev73_plane69_mem : rev73_plane69 ∈ rev73_planes := by decide
def rev73_vertex0 : FractionPoint := fractionRow73[0]!
theorem rev73_vertex0_mem : rev73_vertex0∈fractionRow73 := by decide
def rev73_vertex1 : FractionPoint := fractionRow73[1]!
theorem rev73_vertex1_mem : rev73_vertex1∈fractionRow73 := by decide
def rev73_vertex2 : FractionPoint := fractionRow73[2]!
theorem rev73_vertex2_mem : rev73_vertex2∈fractionRow73 := by decide
def rev73_s0_ll : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev73_s0_ll_mem : rev73_s0_ll.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane4 rev73_vertex0 rev73_vertex1 rev73_s0_ll
    rev73_vertex0_mem rev73_vertex1_mem (by decide)
def rev73_s0_lr : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev73_s0_lr_mem : rev73_s0_lr.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane4 rev73_vertex0 rev73_vertex1 rev73_s0_lr
    rev73_vertex0_mem rev73_vertex1_mem (by decide)
def rev73_s0_ul : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev73_s0_ul_mem : rev73_s0_ul.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane69 rev73_vertex0 rev73_vertex2 rev73_s0_ul
    rev73_vertex0_mem rev73_vertex2_mem (by decide)
def rev73_s0_ur : FractionPoint := ⟨247349711339380133,1063994749732000000,26237285573971392314123,113279052226017165600000⟩
theorem rev73_s0_ur_mem : rev73_s0_ur.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane69 rev73_vertex0 rev73_vertex2 rev73_s0_ur
    rev73_vertex0_mem rev73_vertex2_mem (by decide)
theorem rev73_slab0 (p : Point) (hp : p∈IntegerCarrier rev73_planes)
    (hx0 : rev73_s0_ll.real.1≤p.1) (hx1 : p.1≤rev73_s0_lr.real.1) :
    p∈rationalHull (fractionRow73.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev73_plane4 rev73_plane69 rev73_s0_ll rev73_s0_lr rev73_s0_ul rev73_s0_ur
    (by decide) rev73_s0_ll_mem rev73_s0_lr_mem rev73_s0_ul_mem rev73_s0_ur_mem p
    (hp _ rev73_plane4_mem) (hp _ rev73_plane69_mem) hx0 hx1
def rev73_s1_ll : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev73_s1_ll_mem : rev73_s1_ll.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane27 rev73_vertex1 rev73_vertex2 rev73_s1_ll
    rev73_vertex1_mem rev73_vertex2_mem (by decide)
def rev73_s1_lr : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev73_s1_lr_mem : rev73_s1_lr.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane27 rev73_vertex1 rev73_vertex2 rev73_s1_lr
    rev73_vertex1_mem rev73_vertex2_mem (by decide)
def rev73_s1_ul : FractionPoint := ⟨247349711339380133,1063994749732000000,26237285573971392314123,113279052226017165600000⟩
theorem rev73_s1_ul_mem : rev73_s1_ul.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane69 rev73_vertex0 rev73_vertex2 rev73_s1_ul
    rev73_vertex0_mem rev73_vertex2_mem (by decide)
def rev73_s1_ur : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev73_s1_ur_mem : rev73_s1_ur.real ∈ rationalHull (fractionRow73.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow73 rev73_plane69 rev73_vertex0 rev73_vertex2 rev73_s1_ur
    rev73_vertex0_mem rev73_vertex2_mem (by decide)
theorem rev73_slab1 (p : Point) (hp : p∈IntegerCarrier rev73_planes)
    (hx0 : rev73_s1_ll.real.1≤p.1) (hx1 : p.1≤rev73_s1_lr.real.1) :
    p∈rationalHull (fractionRow73.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev73_plane27 rev73_plane69 rev73_s1_ll rev73_s1_lr rev73_s1_ul rev73_s1_ur
    (by decide) rev73_s1_ll_mem rev73_s1_lr_mem rev73_s1_ul_mem rev73_s1_ur_mem p
    (hp _ rev73_plane27_mem) (hp _ rev73_plane69_mem) hx0 hx1
theorem rev73_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev73_planes) : rev73_s0_ll.real.1≤p.1 := by
  have hc := rev73_plane4.combine_sound rev73_plane69 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev73_plane4_mem) (hp _ rev73_plane69_mem)
  exact (rev73_plane4.combine rev73_plane69 2129316000000 1440116000000).xBoundCheck_sound rev73_s0_ll.nx rev73_s0_ll.dx true (by decide) p hc
theorem rev73_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev73_planes) : p.1≤rev73_s1_lr.real.1 := by
  have hc := rev73_plane27.combine_sound rev73_plane69 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev73_plane27_mem) (hp _ rev73_plane69_mem)
  exact (rev73_plane27.combine rev73_plane69 2129316000000 1861776000000).xBoundCheck_sound rev73_s1_lr.nx rev73_s1_lr.dx false (by decide) p hc
theorem rev73_hull (p : Point) (hp : p∈IntegerCarrier rev73_planes) :
    p∈rationalHull (fractionRow73.map FractionPoint.rational) := by
  have hxlo := rev73_bound0_lo p hp
  have hxhi := rev73_bound0_hi p hp
  by_cases h0 : p.1≤rev73_s0_lr.real.1
  · exact rev73_slab0 p hp hxlo h0
  exact rev73_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull73 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,7,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow73 := by
  rw [← fractionRow73_correct]
  exact rev73_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull73
