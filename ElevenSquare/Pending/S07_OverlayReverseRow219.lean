import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks27
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev219_planes : List IntegerPlane := integerOverlayPlanes ![15,13,8,15]
def rev219_plane14 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-2741459880216)⟩
theorem rev219_plane14_mem : rev219_plane14 ∈ rev219_planes := by decide
def rev219_plane18 : IntegerPlane := ⟨(-2145688000000),699324000000,(-995724727641)⟩
theorem rev219_plane18_mem : rev219_plane18 ∈ rev219_planes := by decide
def rev219_plane36 : IntegerPlane := ⟨1855520000000,287616000000,1643759759600⟩
theorem rev219_plane36_mem : rev219_plane36 ∈ rev219_planes := by decide
def rev219_plane75 : IntegerPlane := ⟨(-2139684000000),15204000000,(-1555517771568)⟩
theorem rev219_plane75_mem : rev219_plane75 ∈ rev219_planes := by decide
def rev219_vertex0 : FractionPoint := fractionRow219[0]!
theorem rev219_vertex0_mem : rev219_vertex0∈fractionRow219 := by decide
def rev219_vertex1 : FractionPoint := fractionRow219[1]!
theorem rev219_vertex1_mem : rev219_vertex1∈fractionRow219 := by decide
def rev219_vertex2 : FractionPoint := fractionRow219[2]!
theorem rev219_vertex2_mem : rev219_vertex2∈fractionRow219 := by decide
def rev219_vertex3 : FractionPoint := fractionRow219[3]!
theorem rev219_vertex3_mem : rev219_vertex3∈fractionRow219 := by decide
def rev219_s0_ll : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev219_s0_ll_mem : rev219_s0_ll.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane14 rev219_vertex2 rev219_vertex3 rev219_s0_ll
    rev219_vertex2_mem rev219_vertex3_mem (by decide)
def rev219_s0_lr : FractionPoint := ⟨89389325943747189,121975777772000000,36013394789711141466507,43914817295475388000000⟩
theorem rev219_s0_lr_mem : rev219_s0_lr.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane14 rev219_vertex2 rev219_vertex3 rev219_s0_lr
    rev219_vertex2_mem rev219_vertex3_mem (by decide)
def rev219_s0_ul : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev219_s0_ul_mem : rev219_s0_ul.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane75 rev219_vertex2 rev219_vertex1 rev219_s0_ul
    rev219_vertex2_mem rev219_vertex1_mem (by decide)
def rev219_s0_ur : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev219_s0_ur_mem : rev219_s0_ur.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane75 rev219_vertex2 rev219_vertex1 rev219_s0_ur
    rev219_vertex2_mem rev219_vertex1_mem (by decide)
theorem rev219_slab0 (p : Point) (hp : p∈IntegerCarrier rev219_planes)
    (hx0 : rev219_s0_ll.real.1≤p.1) (hx1 : p.1≤rev219_s0_lr.real.1) :
    p∈rationalHull (fractionRow219.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev219_plane14 rev219_plane75 rev219_s0_ll rev219_s0_lr rev219_s0_ul rev219_s0_ur
    (by decide) rev219_s0_ll_mem rev219_s0_lr_mem rev219_s0_ul_mem rev219_s0_ur_mem p
    (hp _ rev219_plane14_mem) (hp _ rev219_plane75_mem) hx0 hx1
def rev219_s1_ll : FractionPoint := ⟨89389325943747189,121975777772000000,36013394789711141466507,43914817295475388000000⟩
theorem rev219_s1_ll_mem : rev219_s1_ll.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane14 rev219_vertex2 rev219_vertex3 rev219_s1_ll
    rev219_vertex2_mem rev219_vertex3_mem (by decide)
def rev219_s1_lr : FractionPoint := ⟨7478682361394293,9972624314000000,2853767861565739694559,3590433959145106000000⟩
theorem rev219_s1_lr_mem : rev219_s1_lr.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane14 rev219_vertex2 rev219_vertex3 rev219_s1_lr
    rev219_vertex2_mem rev219_vertex3_mem (by decide)
def rev219_s1_ul : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev219_s1_ul_mem : rev219_s1_ul.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane18 rev219_vertex1 rev219_vertex0 rev219_s1_ul
    rev219_vertex1_mem rev219_vertex0_mem (by decide)
def rev219_s1_ur : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev219_s1_ur_mem : rev219_s1_ur.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane18 rev219_vertex1 rev219_vertex0 rev219_s1_ur
    rev219_vertex1_mem rev219_vertex0_mem (by decide)
theorem rev219_slab1 (p : Point) (hp : p∈IntegerCarrier rev219_planes)
    (hx0 : rev219_s1_ll.real.1≤p.1) (hx1 : p.1≤rev219_s1_lr.real.1) :
    p∈rationalHull (fractionRow219.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev219_plane14 rev219_plane18 rev219_s1_ll rev219_s1_lr rev219_s1_ul rev219_s1_ur
    (by decide) rev219_s1_ll_mem rev219_s1_lr_mem rev219_s1_ul_mem rev219_s1_ur_mem p
    (hp _ rev219_plane14_mem) (hp _ rev219_plane18_mem) hx0 hx1
def rev219_s2_ll : FractionPoint := ⟨7478682361394293,9972624314000000,2853767861565739694559,3590433959145106000000⟩
theorem rev219_s2_ll_mem : rev219_s2_ll.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane14 rev219_vertex2 rev219_vertex3 rev219_s2_ll
    rev219_vertex2_mem rev219_vertex3_mem (by decide)
def rev219_s2_lr : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev219_s2_lr_mem : rev219_s2_lr.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane14 rev219_vertex2 rev219_vertex3 rev219_s2_lr
    rev219_vertex2_mem rev219_vertex3_mem (by decide)
def rev219_s2_ul : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev219_s2_ul_mem : rev219_s2_ul.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane36 rev219_vertex0 rev219_vertex3 rev219_s2_ul
    rev219_vertex0_mem rev219_vertex3_mem (by decide)
def rev219_s2_ur : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev219_s2_ur_mem : rev219_s2_ur.real ∈ rationalHull (fractionRow219.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow219 rev219_plane36 rev219_vertex0 rev219_vertex3 rev219_s2_ur
    rev219_vertex0_mem rev219_vertex3_mem (by decide)
theorem rev219_slab2 (p : Point) (hp : p∈IntegerCarrier rev219_planes)
    (hx0 : rev219_s2_ll.real.1≤p.1) (hx1 : p.1≤rev219_s2_lr.real.1) :
    p∈rationalHull (fractionRow219.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev219_plane14 rev219_plane36 rev219_s2_ll rev219_s2_lr rev219_s2_ul rev219_s2_ur
    (by decide) rev219_s2_ll_mem rev219_s2_lr_mem rev219_s2_ul_mem rev219_s2_ur_mem p
    (hp _ rev219_plane14_mem) (hp _ rev219_plane36_mem) hx0 hx1
theorem rev219_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev219_planes) : rev219_s0_ll.real.1≤p.1 := by
  have hc := rev219_plane14.combine_sound rev219_plane75 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev219_plane14_mem) (hp _ rev219_plane75_mem)
  exact (rev219_plane14.combine rev219_plane75 15204000000 1440116000000).xBoundCheck_sound rev219_s0_ll.nx rev219_s0_ll.dx true (by decide) p hc
theorem rev219_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev219_planes) : p.1≤rev219_s2_lr.real.1 := by
  have hc := rev219_plane14.combine_sound rev219_plane36 287616000000 1440116000000 (by decide) (by decide) p
    (hp _ rev219_plane14_mem) (hp _ rev219_plane36_mem)
  exact (rev219_plane14.combine rev219_plane36 287616000000 1440116000000).xBoundCheck_sound rev219_s2_lr.nx rev219_s2_lr.dx false (by decide) p hc
theorem rev219_hull (p : Point) (hp : p∈IntegerCarrier rev219_planes) :
    p∈rationalHull (fractionRow219.map FractionPoint.rational) := by
  have hxlo := rev219_bound0_lo p hp
  have hxhi := rev219_bound0_hi p hp
  by_cases h0 : p.1≤rev219_s0_lr.real.1
  · exact rev219_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev219_s1_lr.real.1
  · exact rev219_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev219_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull219 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,13,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow219 := by
  rw [← fractionRow219_correct]
  exact rev219_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull219
