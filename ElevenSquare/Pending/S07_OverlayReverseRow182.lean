import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks22
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev182_planes : List IntegerPlane := integerOverlayPlanes ![12,14,0,7]
def rev182_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev182_plane3_mem : rev182_plane3 ∈ rev182_planes := by decide
def rev182_plane17 : IntegerPlane := ⟨1855520000000,(-287616000000),211760240400⟩
theorem rev182_plane17_mem : rev182_plane17 ∈ rev182_planes := by decide
def rev182_plane39 : IntegerPlane := ⟨(-2145688000000),(-699324000000),(-1149963272359)⟩
theorem rev182_plane39_mem : rev182_plane39 ∈ rev182_planes := by decide
def rev182_plane48 : IntegerPlane := ⟨2139684000000,15204000000,584166228432⟩
theorem rev182_plane48_mem : rev182_plane48 ∈ rev182_planes := by decide
def rev182_vertex0 : FractionPoint := fractionRow182[0]!
theorem rev182_vertex0_mem : rev182_vertex0∈fractionRow182 := by decide
def rev182_vertex1 : FractionPoint := fractionRow182[1]!
theorem rev182_vertex1_mem : rev182_vertex1∈fractionRow182 := by decide
def rev182_vertex2 : FractionPoint := fractionRow182[2]!
theorem rev182_vertex2_mem : rev182_vertex2∈fractionRow182 := by decide
def rev182_vertex3 : FractionPoint := fractionRow182[3]!
theorem rev182_vertex3_mem : rev182_vertex3∈fractionRow182 := by decide
def rev182_s0_ll : FractionPoint := ⟨450639272359,2145688000000,1,1⟩
theorem rev182_s0_ll_mem : rev182_s0_ll.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane39 rev182_vertex1 rev182_vertex2 rev182_s0_ll
    rev182_vertex1_mem rev182_vertex2_mem (by decide)
def rev182_s0_lr : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev182_s0_lr_mem : rev182_s0_lr.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane39 rev182_vertex1 rev182_vertex2 rev182_s0_lr
    rev182_vertex1_mem rev182_vertex2_mem (by decide)
def rev182_s0_ul : FractionPoint := ⟨450639272359,2145688000000,1,1⟩
theorem rev182_s0_ul_mem : rev182_s0_ul.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane3 rev182_vertex1 rev182_vertex0 rev182_s0_ul
    rev182_vertex1_mem rev182_vertex0_mem (by decide)
def rev182_s0_ur : FractionPoint := ⟨2493941952605707,9972624314000000,1,1⟩
theorem rev182_s0_ur_mem : rev182_s0_ur.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane3 rev182_vertex1 rev182_vertex0 rev182_s0_ur
    rev182_vertex1_mem rev182_vertex0_mem (by decide)
theorem rev182_slab0 (p : Point) (hp : p∈IntegerCarrier rev182_planes)
    (hx0 : rev182_s0_ll.real.1≤p.1) (hx1 : p.1≤rev182_s0_lr.real.1) :
    p∈rationalHull (fractionRow182.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev182_plane39 rev182_plane3 rev182_s0_ll rev182_s0_lr rev182_s0_ul rev182_s0_ur
    (by decide) rev182_s0_ll_mem rev182_s0_lr_mem rev182_s0_ul_mem rev182_s0_ur_mem p
    (hp _ rev182_plane39_mem) (hp _ rev182_plane3_mem) hx0 hx1
def rev182_s1_ll : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev182_s1_ll_mem : rev182_s1_ll.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane17 rev182_vertex2 rev182_vertex3 rev182_s1_ll
    rev182_vertex2_mem rev182_vertex3_mem (by decide)
def rev182_s1_lr : FractionPoint := ⟨11853379759,44576750000,627729995708449,641049326400000⟩
theorem rev182_s1_lr_mem : rev182_s1_lr.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane17 rev182_vertex2 rev182_vertex3 rev182_s1_lr
    rev182_vertex2_mem rev182_vertex3_mem (by decide)
def rev182_s1_ul : FractionPoint := ⟨2493941952605707,9972624314000000,1,1⟩
theorem rev182_s1_ul_mem : rev182_s1_ul.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane3 rev182_vertex1 rev182_vertex0 rev182_s1_ul
    rev182_vertex1_mem rev182_vertex0_mem (by decide)
def rev182_s1_ur : FractionPoint := ⟨11853379759,44576750000,1,1⟩
theorem rev182_s1_ur_mem : rev182_s1_ur.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane3 rev182_vertex1 rev182_vertex0 rev182_s1_ur
    rev182_vertex1_mem rev182_vertex0_mem (by decide)
theorem rev182_slab1 (p : Point) (hp : p∈IntegerCarrier rev182_planes)
    (hx0 : rev182_s1_ll.real.1≤p.1) (hx1 : p.1≤rev182_s1_lr.real.1) :
    p∈rationalHull (fractionRow182.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev182_plane17 rev182_plane3 rev182_s1_ll rev182_s1_lr rev182_s1_ul rev182_s1_ur
    (by decide) rev182_s1_ll_mem rev182_s1_lr_mem rev182_s1_ul_mem rev182_s1_ur_mem p
    (hp _ rev182_plane17_mem) (hp _ rev182_plane3_mem) hx0 hx1
def rev182_s2_ll : FractionPoint := ⟨11853379759,44576750000,627729995708449,641049326400000⟩
theorem rev182_s2_ll_mem : rev182_s2_ll.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane17 rev182_vertex2 rev182_vertex3 rev182_s2_ll
    rev182_vertex2_mem rev182_vertex3_mem (by decide)
def rev182_s2_lr : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev182_s2_lr_mem : rev182_s2_lr.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane17 rev182_vertex2 rev182_vertex3 rev182_s2_lr
    rev182_vertex2_mem rev182_vertex3_mem (by decide)
def rev182_s2_ul : FractionPoint := ⟨11853379759,44576750000,1,1⟩
theorem rev182_s2_ul_mem : rev182_s2_ul.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane48 rev182_vertex0 rev182_vertex3 rev182_s2_ul
    rev182_vertex0_mem rev182_vertex3_mem (by decide)
def rev182_s2_ur : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev182_s2_ur_mem : rev182_s2_ur.real ∈ rationalHull (fractionRow182.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow182 rev182_plane48 rev182_vertex0 rev182_vertex3 rev182_s2_ur
    rev182_vertex0_mem rev182_vertex3_mem (by decide)
theorem rev182_slab2 (p : Point) (hp : p∈IntegerCarrier rev182_planes)
    (hx0 : rev182_s2_ll.real.1≤p.1) (hx1 : p.1≤rev182_s2_lr.real.1) :
    p∈rationalHull (fractionRow182.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev182_plane17 rev182_plane48 rev182_s2_ll rev182_s2_lr rev182_s2_ul rev182_s2_ur
    (by decide) rev182_s2_ll_mem rev182_s2_lr_mem rev182_s2_ul_mem rev182_s2_ur_mem p
    (hp _ rev182_plane17_mem) (hp _ rev182_plane48_mem) hx0 hx1
theorem rev182_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev182_planes) : rev182_s0_ll.real.1≤p.1 := by
  have hc := rev182_plane3.combine_sound rev182_plane39 699324000000 1 (by decide) (by decide) p
    (hp _ rev182_plane3_mem) (hp _ rev182_plane39_mem)
  exact (rev182_plane3.combine rev182_plane39 699324000000 1).xBoundCheck_sound rev182_s0_ll.nx rev182_s0_ll.dx true (by decide) p hc
theorem rev182_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev182_planes) : p.1≤rev182_s2_lr.real.1 := by
  have hc := rev182_plane17.combine_sound rev182_plane48 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev182_plane17_mem) (hp _ rev182_plane48_mem)
  exact (rev182_plane17.combine rev182_plane48 15204000000 287616000000).xBoundCheck_sound rev182_s2_lr.nx rev182_s2_lr.dx false (by decide) p hc
theorem rev182_hull (p : Point) (hp : p∈IntegerCarrier rev182_planes) :
    p∈rationalHull (fractionRow182.map FractionPoint.rational) := by
  have hxlo := rev182_bound0_lo p hp
  have hxhi := rev182_bound0_hi p hp
  by_cases h0 : p.1≤rev182_s0_lr.real.1
  · exact rev182_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev182_s1_lr.real.1
  · exact rev182_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev182_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull182 (p : Point)
    (hp : ∀ g, ClosedCell ((![12,14,0,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow182 := by
  rw [← fractionRow182_correct]
  exact rev182_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull182
