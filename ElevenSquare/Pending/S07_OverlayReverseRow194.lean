import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev194_planes : List IntegerPlane := integerOverlayPlanes ![13,13,4,11]
def rev194_plane14 : IntegerPlane := ⟨2099728000000,(-1393416000000),(-33871860516)⟩
theorem rev194_plane14_mem : rev194_plane14 ∈ rev194_planes := by decide
def rev194_plane18 : IntegerPlane := ⟨2083356000000,746024000000,1711863292059⟩
theorem rev194_plane18_mem : rev194_plane18 ∈ rev194_planes := by decide
def rev194_plane34 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-2133599860516)⟩
theorem rev194_plane34_mem : rev194_plane34 ∈ rev194_planes := by decide
def rev194_plane38 : IntegerPlane := ⟨(-2083356000000),746024000000,(-371492707941)⟩
theorem rev194_plane38_mem : rev194_plane38 ∈ rev194_planes := by decide
def rev194_vertex0 : FractionPoint := fractionRow194[0]!
theorem rev194_vertex0_mem : rev194_vertex0∈fractionRow194 := by decide
def rev194_vertex1 : FractionPoint := fractionRow194[1]!
theorem rev194_vertex1_mem : rev194_vertex1∈fractionRow194 := by decide
def rev194_vertex2 : FractionPoint := fractionRow194[2]!
theorem rev194_vertex2_mem : rev194_vertex2∈fractionRow194 := by decide
def rev194_vertex3 : FractionPoint := fractionRow194[3]!
theorem rev194_vertex3_mem : rev194_vertex3∈fractionRow194 := by decide
def rev194_s0_ll : FractionPoint := ⟨52734014636747621,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev194_s0_ll_mem : rev194_s0_ll.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane34 rev194_vertex0 rev194_vertex1 rev194_s0_ll
    rev194_vertex0_mem rev194_vertex1_mem (by decide)
def rev194_s0_lr : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev194_s0_lr_mem : rev194_s0_lr.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane34 rev194_vertex0 rev194_vertex1 rev194_s0_lr
    rev194_vertex0_mem rev194_vertex1_mem (by decide)
def rev194_s0_ul : FractionPoint := ⟨52734014636747621,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev194_s0_ul_mem : rev194_s0_ul.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane38 rev194_vertex0 rev194_vertex3 rev194_s0_ul
    rev194_vertex0_mem rev194_vertex3_mem (by decide)
def rev194_s0_ur : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev194_s0_ur_mem : rev194_s0_ur.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane38 rev194_vertex0 rev194_vertex3 rev194_s0_ur
    rev194_vertex0_mem rev194_vertex3_mem (by decide)
theorem rev194_slab0 (p : Point) (hp : p∈IntegerCarrier rev194_planes)
    (hx0 : rev194_s0_ll.real.1≤p.1) (hx1 : p.1≤rev194_s0_lr.real.1) :
    p∈rationalHull (fractionRow194.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev194_plane34 rev194_plane38 rev194_s0_ll rev194_s0_lr rev194_s0_ul rev194_s0_ur
    (by decide) rev194_s0_ll_mem rev194_s0_lr_mem rev194_s0_ul_mem rev194_s0_ur_mem p
    (hp _ rev194_plane34_mem) (hp _ rev194_plane38_mem) hx0 hx1
def rev194_s1_ll : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev194_s1_ll_mem : rev194_s1_ll.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane14 rev194_vertex1 rev194_vertex2 rev194_s1_ll
    rev194_vertex1_mem rev194_vertex2_mem (by decide)
def rev194_s1_lr : FractionPoint := ⟨59001712002452379,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev194_s1_lr_mem : rev194_s1_lr.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane14 rev194_vertex1 rev194_vertex2 rev194_s1_lr
    rev194_vertex1_mem rev194_vertex2_mem (by decide)
def rev194_s1_ul : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev194_s1_ul_mem : rev194_s1_ul.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane18 rev194_vertex3 rev194_vertex2 rev194_s1_ul
    rev194_vertex3_mem rev194_vertex2_mem (by decide)
def rev194_s1_ur : FractionPoint := ⟨59001712002452379,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev194_s1_ur_mem : rev194_s1_ur.real ∈ rationalHull (fractionRow194.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow194 rev194_plane18 rev194_vertex3 rev194_vertex2 rev194_s1_ur
    rev194_vertex3_mem rev194_vertex2_mem (by decide)
theorem rev194_slab1 (p : Point) (hp : p∈IntegerCarrier rev194_planes)
    (hx0 : rev194_s1_ll.real.1≤p.1) (hx1 : p.1≤rev194_s1_lr.real.1) :
    p∈rationalHull (fractionRow194.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev194_plane14 rev194_plane18 rev194_s1_ll rev194_s1_lr rev194_s1_ul rev194_s1_ur
    (by decide) rev194_s1_ll_mem rev194_s1_lr_mem rev194_s1_ul_mem rev194_s1_ur_mem p
    (hp _ rev194_plane14_mem) (hp _ rev194_plane18_mem) hx0 hx1
theorem rev194_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev194_planes) : rev194_s0_ll.real.1≤p.1 := by
  have hc := rev194_plane34.combine_sound rev194_plane38 746024000000 1393416000000 (by decide) (by decide) p
    (hp _ rev194_plane34_mem) (hp _ rev194_plane38_mem)
  exact (rev194_plane34.combine rev194_plane38 746024000000 1393416000000).xBoundCheck_sound rev194_s0_ll.nx rev194_s0_ll.dx true (by decide) p hc
theorem rev194_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev194_planes) : p.1≤rev194_s1_lr.real.1 := by
  have hc := rev194_plane14.combine_sound rev194_plane18 746024000000 1393416000000 (by decide) (by decide) p
    (hp _ rev194_plane14_mem) (hp _ rev194_plane18_mem)
  exact (rev194_plane14.combine rev194_plane18 746024000000 1393416000000).xBoundCheck_sound rev194_s1_lr.nx rev194_s1_lr.dx false (by decide) p hc
theorem rev194_hull (p : Point) (hp : p∈IntegerCarrier rev194_planes) :
    p∈rationalHull (fractionRow194.map FractionPoint.rational) := by
  have hxlo := rev194_bound0_lo p hp
  have hxhi := rev194_bound0_hi p hp
  by_cases h0 : p.1≤rev194_s0_lr.real.1
  · exact rev194_slab0 p hp hxlo h0
  exact rev194_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull194 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,13,4,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow194 := by
  rw [← fractionRow194_correct]
  exact rev194_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull194
