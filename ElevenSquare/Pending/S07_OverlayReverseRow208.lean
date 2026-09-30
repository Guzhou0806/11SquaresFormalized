import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev208_planes : List IntegerPlane := integerOverlayPlanes ![15,8,8,10]
def rev208_plane14 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-2741459880216)⟩
theorem rev208_plane14_mem : rev208_plane14 ∈ rev208_planes := by decide
def rev208_plane56 : IntegerPlane := ⟨1861776000000,(-202532000000),1275872260553⟩
theorem rev208_plane56_mem : rev208_plane56 ∈ rev208_planes := by decide
def rev208_plane79 : IntegerPlane := ⟨1440116000000,2129316000000,2741459880216⟩
theorem rev208_plane79_mem : rev208_plane79 ∈ rev208_planes := by decide
def rev208_vertex0 : FractionPoint := fractionRow208[0]!
theorem rev208_vertex0_mem : rev208_vertex0∈fractionRow208 := by decide
def rev208_vertex1 : FractionPoint := fractionRow208[1]!
theorem rev208_vertex1_mem : rev208_vertex1∈fractionRow208 := by decide
def rev208_vertex2 : FractionPoint := fractionRow208[2]!
theorem rev208_vertex2_mem : rev208_vertex2∈fractionRow208 := by decide
def rev208_s0_ll : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev208_s0_ll_mem : rev208_s0_ll.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane14 rev208_vertex0 rev208_vertex1 rev208_s0_ll
    rev208_vertex0_mem rev208_vertex1_mem (by decide)
def rev208_s0_lr : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev208_s0_lr_mem : rev208_s0_lr.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane14 rev208_vertex0 rev208_vertex1 rev208_s0_lr
    rev208_vertex0_mem rev208_vertex1_mem (by decide)
def rev208_s0_ul : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev208_s0_ul_mem : rev208_s0_ul.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane79 rev208_vertex0 rev208_vertex2 rev208_s0_ul
    rev208_vertex0_mem rev208_vertex2_mem (by decide)
def rev208_s0_ur : FractionPoint := ⟨119631870441922553,155621401706400000,317932573184667028330543,414208925744831028000000⟩
theorem rev208_s0_ur_mem : rev208_s0_ur.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane79 rev208_vertex0 rev208_vertex2 rev208_s0_ur
    rev208_vertex0_mem rev208_vertex2_mem (by decide)
theorem rev208_slab0 (p : Point) (hp : p∈IntegerCarrier rev208_planes)
    (hx0 : rev208_s0_ll.real.1≤p.1) (hx1 : p.1≤rev208_s0_lr.real.1) :
    p∈rationalHull (fractionRow208.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev208_plane14 rev208_plane79 rev208_s0_ll rev208_s0_lr rev208_s0_ul rev208_s0_ur
    (by decide) rev208_s0_ll_mem rev208_s0_lr_mem rev208_s0_ul_mem rev208_s0_ur_mem p
    (hp _ rev208_plane14_mem) (hp _ rev208_plane79_mem) hx0 hx1
def rev208_s1_ll : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev208_s1_ll_mem : rev208_s1_ll.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane56 rev208_vertex1 rev208_vertex2 rev208_s1_ll
    rev208_vertex1_mem rev208_vertex2_mem (by decide)
def rev208_s1_lr : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev208_s1_lr_mem : rev208_s1_lr.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane56 rev208_vertex1 rev208_vertex2 rev208_s1_lr
    rev208_vertex1_mem rev208_vertex2_mem (by decide)
def rev208_s1_ul : FractionPoint := ⟨119631870441922553,155621401706400000,317932573184667028330543,414208925744831028000000⟩
theorem rev208_s1_ul_mem : rev208_s1_ul.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane79 rev208_vertex0 rev208_vertex2 rev208_s1_ul
    rev208_vertex0_mem rev208_vertex2_mem (by decide)
def rev208_s1_ur : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev208_s1_ur_mem : rev208_s1_ur.real ∈ rationalHull (fractionRow208.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow208 rev208_plane79 rev208_vertex0 rev208_vertex2 rev208_s1_ur
    rev208_vertex0_mem rev208_vertex2_mem (by decide)
theorem rev208_slab1 (p : Point) (hp : p∈IntegerCarrier rev208_planes)
    (hx0 : rev208_s1_ll.real.1≤p.1) (hx1 : p.1≤rev208_s1_lr.real.1) :
    p∈rationalHull (fractionRow208.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev208_plane56 rev208_plane79 rev208_s1_ll rev208_s1_lr rev208_s1_ul rev208_s1_ur
    (by decide) rev208_s1_ll_mem rev208_s1_lr_mem rev208_s1_ul_mem rev208_s1_ur_mem p
    (hp _ rev208_plane56_mem) (hp _ rev208_plane79_mem) hx0 hx1
theorem rev208_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev208_planes) : rev208_s0_ll.real.1≤p.1 := by
  have hc := rev208_plane14.combine_sound rev208_plane79 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev208_plane14_mem) (hp _ rev208_plane79_mem)
  exact (rev208_plane14.combine rev208_plane79 2129316000000 1440116000000).xBoundCheck_sound rev208_s0_ll.nx rev208_s0_ll.dx true (by decide) p hc
theorem rev208_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev208_planes) : p.1≤rev208_s1_lr.real.1 := by
  have hc := rev208_plane56.combine_sound rev208_plane79 2129316000000 202532000000 (by decide) (by decide) p
    (hp _ rev208_plane56_mem) (hp _ rev208_plane79_mem)
  exact (rev208_plane56.combine rev208_plane79 2129316000000 202532000000).xBoundCheck_sound rev208_s1_lr.nx rev208_s1_lr.dx false (by decide) p hc
theorem rev208_hull (p : Point) (hp : p∈IntegerCarrier rev208_planes) :
    p∈rationalHull (fractionRow208.map FractionPoint.rational) := by
  have hxlo := rev208_bound0_lo p hp
  have hxhi := rev208_bound0_hi p hp
  by_cases h0 : p.1≤rev208_s0_lr.real.1
  · exact rev208_slab0 p hp hxlo h0
  exact rev208_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull208 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,8,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow208 := by
  rw [← fractionRow208_correct]
  exact rev208_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull208
