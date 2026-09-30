import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev126_planes : List IntegerPlane := integerOverlayPlanes ![8,15,5,7]
def rev126_plane34 : IntegerPlane := ⟨2129316000000,(-1440116000000),(-612143880216)⟩
theorem rev126_plane34_mem : rev126_plane34 ∈ rev126_planes := by decide
def rev126_plane44 : IntegerPlane := ⟨(-1440116000000),2129316000000,1301343880216⟩
theorem rev126_plane44_mem : rev126_plane44 ∈ rev126_planes := by decide
def rev126_plane67 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-585903739447)⟩
theorem rev126_plane67_mem : rev126_plane67 ∈ rev126_planes := by decide
def rev126_vertex0 : FractionPoint := fractionRow126[0]!
theorem rev126_vertex0_mem : rev126_vertex0∈fractionRow126 := by decide
def rev126_vertex1 : FractionPoint := fractionRow126[1]!
theorem rev126_vertex1_mem : rev126_vertex1∈fractionRow126 := by decide
def rev126_vertex2 : FractionPoint := fractionRow126[2]!
theorem rev126_vertex2_mem : rev126_vertex2∈fractionRow126 := by decide
def rev126_s0_ll : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev126_s0_ll_mem : rev126_s0_ll.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane67 rev126_vertex2 rev126_vertex0 rev126_s0_ll
    rev126_vertex2_mem rev126_vertex0_mem (by decide)
def rev126_s0_lr : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev126_s0_lr_mem : rev126_s0_lr.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane67 rev126_vertex2 rev126_vertex0 rev126_s0_lr
    rev126_vertex2_mem rev126_vertex0_mem (by decide)
def rev126_s0_ul : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev126_s0_ul_mem : rev126_s0_ul.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane44 rev126_vertex2 rev126_vertex1 rev126_s0_ul
    rev126_vertex2_mem rev126_vertex1_mem (by decide)
def rev126_s0_ur : FractionPoint := ⟨35989531264477447,155621401706400000,317932573184667028330543,414208925744831028000000⟩
theorem rev126_s0_ur_mem : rev126_s0_ur.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane44 rev126_vertex2 rev126_vertex1 rev126_s0_ur
    rev126_vertex2_mem rev126_vertex1_mem (by decide)
theorem rev126_slab0 (p : Point) (hp : p∈IntegerCarrier rev126_planes)
    (hx0 : rev126_s0_ll.real.1≤p.1) (hx1 : p.1≤rev126_s0_lr.real.1) :
    p∈rationalHull (fractionRow126.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev126_plane67 rev126_plane44 rev126_s0_ll rev126_s0_lr rev126_s0_ul rev126_s0_ur
    (by decide) rev126_s0_ll_mem rev126_s0_lr_mem rev126_s0_ul_mem rev126_s0_ur_mem p
    (hp _ rev126_plane67_mem) (hp _ rev126_plane44_mem) hx0 hx1
def rev126_s1_ll : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev126_s1_ll_mem : rev126_s1_ll.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane34 rev126_vertex0 rev126_vertex1 rev126_s1_ll
    rev126_vertex0_mem rev126_vertex1_mem (by decide)
def rev126_s1_lr : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev126_s1_lr_mem : rev126_s1_lr.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane34 rev126_vertex0 rev126_vertex1 rev126_s1_lr
    rev126_vertex0_mem rev126_vertex1_mem (by decide)
def rev126_s1_ul : FractionPoint := ⟨35989531264477447,155621401706400000,317932573184667028330543,414208925744831028000000⟩
theorem rev126_s1_ul_mem : rev126_s1_ul.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane44 rev126_vertex2 rev126_vertex1 rev126_s1_ul
    rev126_vertex2_mem rev126_vertex1_mem (by decide)
def rev126_s1_ur : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev126_s1_ur_mem : rev126_s1_ur.real ∈ rationalHull (fractionRow126.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow126 rev126_plane44 rev126_vertex2 rev126_vertex1 rev126_s1_ur
    rev126_vertex2_mem rev126_vertex1_mem (by decide)
theorem rev126_slab1 (p : Point) (hp : p∈IntegerCarrier rev126_planes)
    (hx0 : rev126_s1_ll.real.1≤p.1) (hx1 : p.1≤rev126_s1_lr.real.1) :
    p∈rationalHull (fractionRow126.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev126_plane34 rev126_plane44 rev126_s1_ll rev126_s1_lr rev126_s1_ul rev126_s1_ur
    (by decide) rev126_s1_ll_mem rev126_s1_lr_mem rev126_s1_ul_mem rev126_s1_ur_mem p
    (hp _ rev126_plane34_mem) (hp _ rev126_plane44_mem) hx0 hx1
theorem rev126_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev126_planes) : rev126_s0_ll.real.1≤p.1 := by
  have hc := rev126_plane44.combine_sound rev126_plane67 202532000000 2129316000000 (by decide) (by decide) p
    (hp _ rev126_plane44_mem) (hp _ rev126_plane67_mem)
  exact (rev126_plane44.combine rev126_plane67 202532000000 2129316000000).xBoundCheck_sound rev126_s0_ll.nx rev126_s0_ll.dx true (by decide) p hc
theorem rev126_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev126_planes) : p.1≤rev126_s1_lr.real.1 := by
  have hc := rev126_plane34.combine_sound rev126_plane44 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev126_plane34_mem) (hp _ rev126_plane44_mem)
  exact (rev126_plane34.combine rev126_plane44 2129316000000 1440116000000).xBoundCheck_sound rev126_s1_lr.nx rev126_s1_lr.dx false (by decide) p hc
theorem rev126_hull (p : Point) (hp : p∈IntegerCarrier rev126_planes) :
    p∈rationalHull (fractionRow126.map FractionPoint.rational) := by
  have hxlo := rev126_bound0_lo p hp
  have hxhi := rev126_bound0_hi p hp
  by_cases h0 : p.1≤rev126_s0_lr.real.1
  · exact rev126_slab0 p hp hxlo h0
  exact rev126_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull126 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,5,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow126 := by
  rw [← fractionRow126_correct]
  exact rev126_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull126
