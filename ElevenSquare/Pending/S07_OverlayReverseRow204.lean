import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev204_planes : List IntegerPlane := integerOverlayPlanes ![14,13,8,15]
def rev204_plane19 : IntegerPlane := ⟨2145688000000,(-699324000000),995724727641⟩
theorem rev204_plane19_mem : rev204_plane19 ∈ rev204_planes := by decide
def rev204_plane36 : IntegerPlane := ⟨1855520000000,287616000000,1643759759600⟩
theorem rev204_plane36_mem : rev204_plane36 ∈ rev204_planes := by decide
def rev204_plane75 : IntegerPlane := ⟨(-2139684000000),15204000000,(-1555517771568)⟩
theorem rev204_plane75_mem : rev204_plane75 ∈ rev204_planes := by decide
def rev204_vertex0 : FractionPoint := fractionRow204[0]!
theorem rev204_vertex0_mem : rev204_vertex0∈fractionRow204 := by decide
def rev204_vertex1 : FractionPoint := fractionRow204[1]!
theorem rev204_vertex1_mem : rev204_vertex1∈fractionRow204 := by decide
def rev204_vertex2 : FractionPoint := fractionRow204[2]!
theorem rev204_vertex2_mem : rev204_vertex2∈fractionRow204 := by decide
def rev204_s0_ll : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev204_s0_ll_mem : rev204_s0_ll.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane19 rev204_vertex0 rev204_vertex1 rev204_s0_ll
    rev204_vertex0_mem rev204_vertex1_mem (by decide)
def rev204_s0_lr : FractionPoint := ⟨351475835396027,478882946000000,27732189132146067119,33489433732850400000⟩
theorem rev204_s0_lr_mem : rev204_s0_lr.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane19 rev204_vertex0 rev204_vertex1 rev204_s0_lr
    rev204_vertex0_mem rev204_vertex1_mem (by decide)
def rev204_s0_ul : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev204_s0_ul_mem : rev204_s0_ul.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane75 rev204_vertex0 rev204_vertex2 rev204_s0_ul
    rev204_vertex0_mem rev204_vertex2_mem (by decide)
def rev204_s0_ur : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev204_s0_ur_mem : rev204_s0_ur.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane75 rev204_vertex0 rev204_vertex2 rev204_s0_ur
    rev204_vertex0_mem rev204_vertex2_mem (by decide)
theorem rev204_slab0 (p : Point) (hp : p∈IntegerCarrier rev204_planes)
    (hx0 : rev204_s0_ll.real.1≤p.1) (hx1 : p.1≤rev204_s0_lr.real.1) :
    p∈rationalHull (fractionRow204.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev204_plane19 rev204_plane75 rev204_s0_ll rev204_s0_lr rev204_s0_ul rev204_s0_ur
    (by decide) rev204_s0_ll_mem rev204_s0_lr_mem rev204_s0_ul_mem rev204_s0_ur_mem p
    (hp _ rev204_plane19_mem) (hp _ rev204_plane75_mem) hx0 hx1
def rev204_s1_ll : FractionPoint := ⟨351475835396027,478882946000000,27732189132146067119,33489433732850400000⟩
theorem rev204_s1_ll_mem : rev204_s1_ll.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane19 rev204_vertex0 rev204_vertex1 rev204_s1_ll
    rev204_vertex0_mem rev204_vertex1_mem (by decide)
def rev204_s1_lr : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev204_s1_lr_mem : rev204_s1_lr.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane19 rev204_vertex0 rev204_vertex1 rev204_s1_lr
    rev204_vertex0_mem rev204_vertex1_mem (by decide)
def rev204_s1_ul : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev204_s1_ul_mem : rev204_s1_ul.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane36 rev204_vertex2 rev204_vertex1 rev204_s1_ul
    rev204_vertex2_mem rev204_vertex1_mem (by decide)
def rev204_s1_ur : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev204_s1_ur_mem : rev204_s1_ur.real ∈ rationalHull (fractionRow204.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow204 rev204_plane36 rev204_vertex2 rev204_vertex1 rev204_s1_ur
    rev204_vertex2_mem rev204_vertex1_mem (by decide)
theorem rev204_slab1 (p : Point) (hp : p∈IntegerCarrier rev204_planes)
    (hx0 : rev204_s1_ll.real.1≤p.1) (hx1 : p.1≤rev204_s1_lr.real.1) :
    p∈rationalHull (fractionRow204.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev204_plane19 rev204_plane36 rev204_s1_ll rev204_s1_lr rev204_s1_ul rev204_s1_ur
    (by decide) rev204_s1_ll_mem rev204_s1_lr_mem rev204_s1_ul_mem rev204_s1_ur_mem p
    (hp _ rev204_plane19_mem) (hp _ rev204_plane36_mem) hx0 hx1
theorem rev204_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev204_planes) : rev204_s0_ll.real.1≤p.1 := by
  have hc := rev204_plane19.combine_sound rev204_plane75 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev204_plane19_mem) (hp _ rev204_plane75_mem)
  exact (rev204_plane19.combine rev204_plane75 15204000000 699324000000).xBoundCheck_sound rev204_s0_ll.nx rev204_s0_ll.dx true (by decide) p hc
theorem rev204_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev204_planes) : p.1≤rev204_s1_lr.real.1 := by
  have hc := rev204_plane19.combine_sound rev204_plane36 287616000000 699324000000 (by decide) (by decide) p
    (hp _ rev204_plane19_mem) (hp _ rev204_plane36_mem)
  exact (rev204_plane19.combine rev204_plane36 287616000000 699324000000).xBoundCheck_sound rev204_s1_lr.nx rev204_s1_lr.dx false (by decide) p hc
theorem rev204_hull (p : Point) (hp : p∈IntegerCarrier rev204_planes) :
    p∈rationalHull (fractionRow204.map FractionPoint.rational) := by
  have hxlo := rev204_bound0_lo p hp
  have hxhi := rev204_bound0_hi p hp
  by_cases h0 : p.1≤rev204_s0_lr.real.1
  · exact rev204_slab0 p hp hxlo h0
  exact rev204_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull204 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,13,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow204 := by
  rw [← fractionRow204_correct]
  exact rev204_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull204
