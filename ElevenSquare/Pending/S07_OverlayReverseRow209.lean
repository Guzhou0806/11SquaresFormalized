import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev209_planes : List IntegerPlane := integerOverlayPlanes ![15,8,8,15]
def rev209_plane14 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-2741459880216)⟩
theorem rev209_plane14_mem : rev209_plane14 ∈ rev209_planes := by decide
def rev209_plane36 : IntegerPlane := ⟨(-202532000000),1861776000000,1275872260553⟩
theorem rev209_plane36_mem : rev209_plane36 ∈ rev209_planes := by decide
def rev209_plane56 : IntegerPlane := ⟨1861776000000,(-202532000000),1275872260553⟩
theorem rev209_plane56_mem : rev209_plane56 ∈ rev209_planes := by decide
def rev209_plane74 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-2741459880216)⟩
theorem rev209_plane74_mem : rev209_plane74 ∈ rev209_planes := by decide
def rev209_vertex0 : FractionPoint := fractionRow209[0]!
theorem rev209_vertex0_mem : rev209_vertex0∈fractionRow209 := by decide
def rev209_vertex1 : FractionPoint := fractionRow209[1]!
theorem rev209_vertex1_mem : rev209_vertex1∈fractionRow209 := by decide
def rev209_vertex2 : FractionPoint := fractionRow209[2]!
theorem rev209_vertex2_mem : rev209_vertex2∈fractionRow209 := by decide
def rev209_vertex3 : FractionPoint := fractionRow209[3]!
theorem rev209_vertex3_mem : rev209_vertex3∈fractionRow209 := by decide
def rev209_s0_ll : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev209_s0_ll_mem : rev209_s0_ll.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane14 rev209_vertex1 rev209_vertex2 rev209_s0_ll
    rev209_vertex1_mem rev209_vertex2_mem (by decide)
def rev209_s0_lr : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev209_s0_lr_mem : rev209_s0_lr.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane14 rev209_vertex1 rev209_vertex2 rev209_s0_lr
    rev209_vertex1_mem rev209_vertex2_mem (by decide)
def rev209_s0_ul : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev209_s0_ul_mem : rev209_s0_ul.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane36 rev209_vertex1 rev209_vertex0 rev209_s0_ul
    rev209_vertex1_mem rev209_vertex0_mem (by decide)
def rev209_s0_ur : FractionPoint := ⟨342682485027,446179000000,638671578398765351,830685353904000000⟩
theorem rev209_s0_ur_mem : rev209_s0_ur.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane36 rev209_vertex1 rev209_vertex0 rev209_s0_ur
    rev209_vertex1_mem rev209_vertex0_mem (by decide)
theorem rev209_slab0 (p : Point) (hp : p∈IntegerCarrier rev209_planes)
    (hx0 : rev209_s0_ll.real.1≤p.1) (hx1 : p.1≤rev209_s0_lr.real.1) :
    p∈rationalHull (fractionRow209.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev209_plane14 rev209_plane36 rev209_s0_ll rev209_s0_lr rev209_s0_ul rev209_s0_ur
    (by decide) rev209_s0_ll_mem rev209_s0_lr_mem rev209_s0_ul_mem rev209_s0_ur_mem p
    (hp _ rev209_plane14_mem) (hp _ rev209_plane36_mem) hx0 hx1
def rev209_s1_ll : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev209_s1_ll_mem : rev209_s1_ll.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane74 rev209_vertex2 rev209_vertex3 rev209_s1_ll
    rev209_vertex2_mem rev209_vertex3_mem (by decide)
def rev209_s1_lr : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev209_s1_lr_mem : rev209_s1_lr.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane74 rev209_vertex2 rev209_vertex3 rev209_s1_lr
    rev209_vertex2_mem rev209_vertex3_mem (by decide)
def rev209_s1_ul : FractionPoint := ⟨342682485027,446179000000,638671578398765351,830685353904000000⟩
theorem rev209_s1_ul_mem : rev209_s1_ul.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane36 rev209_vertex1 rev209_vertex0 rev209_s1_ul
    rev209_vertex1_mem rev209_vertex0_mem (by decide)
def rev209_s1_ur : FractionPoint := ⟨163598428540578933,212798949946400000,190398871400374124151697,247614986147130504000000⟩
theorem rev209_s1_ur_mem : rev209_s1_ur.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane36 rev209_vertex1 rev209_vertex0 rev209_s1_ur
    rev209_vertex1_mem rev209_vertex0_mem (by decide)
theorem rev209_slab1 (p : Point) (hp : p∈IntegerCarrier rev209_planes)
    (hx0 : rev209_s1_ll.real.1≤p.1) (hx1 : p.1≤rev209_s1_lr.real.1) :
    p∈rationalHull (fractionRow209.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev209_plane74 rev209_plane36 rev209_s1_ll rev209_s1_lr rev209_s1_ul rev209_s1_ur
    (by decide) rev209_s1_ll_mem rev209_s1_lr_mem rev209_s1_ul_mem rev209_s1_ur_mem p
    (hp _ rev209_plane74_mem) (hp _ rev209_plane36_mem) hx0 hx1
def rev209_s2_ll : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev209_s2_ll_mem : rev209_s2_ll.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane56 rev209_vertex3 rev209_vertex0 rev209_s2_ll
    rev209_vertex3_mem rev209_vertex0_mem (by decide)
def rev209_s2_lr : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev209_s2_lr_mem : rev209_s2_lr.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane56 rev209_vertex3 rev209_vertex0 rev209_s2_lr
    rev209_vertex3_mem rev209_vertex0_mem (by decide)
def rev209_s2_ul : FractionPoint := ⟨163598428540578933,212798949946400000,190398871400374124151697,247614986147130504000000⟩
theorem rev209_s2_ul_mem : rev209_s2_ul.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane36 rev209_vertex1 rev209_vertex0 rev209_s2_ul
    rev209_vertex1_mem rev209_vertex0_mem (by decide)
def rev209_s2_ur : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev209_s2_ur_mem : rev209_s2_ur.real ∈ rationalHull (fractionRow209.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow209 rev209_plane36 rev209_vertex1 rev209_vertex0 rev209_s2_ur
    rev209_vertex1_mem rev209_vertex0_mem (by decide)
theorem rev209_slab2 (p : Point) (hp : p∈IntegerCarrier rev209_planes)
    (hx0 : rev209_s2_ll.real.1≤p.1) (hx1 : p.1≤rev209_s2_lr.real.1) :
    p∈rationalHull (fractionRow209.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev209_plane56 rev209_plane36 rev209_s2_ll rev209_s2_lr rev209_s2_ul rev209_s2_ur
    (by decide) rev209_s2_ll_mem rev209_s2_lr_mem rev209_s2_ul_mem rev209_s2_ur_mem p
    (hp _ rev209_plane56_mem) (hp _ rev209_plane36_mem) hx0 hx1
theorem rev209_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev209_planes) : rev209_s0_ll.real.1≤p.1 := by
  have hc := rev209_plane14.combine_sound rev209_plane36 1861776000000 1440116000000 (by decide) (by decide) p
    (hp _ rev209_plane14_mem) (hp _ rev209_plane36_mem)
  exact (rev209_plane14.combine rev209_plane36 1861776000000 1440116000000).xBoundCheck_sound rev209_s0_ll.nx rev209_s0_ll.dx true (by decide) p hc
theorem rev209_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev209_planes) : p.1≤rev209_s2_lr.real.1 := by
  have hc := rev209_plane36.combine_sound rev209_plane56 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev209_plane36_mem) (hp _ rev209_plane56_mem)
  exact (rev209_plane36.combine rev209_plane56 202532000000 1861776000000).xBoundCheck_sound rev209_s2_lr.nx rev209_s2_lr.dx false (by decide) p hc
theorem rev209_hull (p : Point) (hp : p∈IntegerCarrier rev209_planes) :
    p∈rationalHull (fractionRow209.map FractionPoint.rational) := by
  have hxlo := rev209_bound0_lo p hp
  have hxhi := rev209_bound0_hi p hp
  by_cases h0 : p.1≤rev209_s0_lr.real.1
  · exact rev209_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev209_s1_lr.real.1
  · exact rev209_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev209_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull209 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow209 := by
  rw [← fractionRow209_correct]
  exact rev209_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull209
