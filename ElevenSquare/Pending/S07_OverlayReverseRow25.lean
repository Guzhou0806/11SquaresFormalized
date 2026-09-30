import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev25_planes : List IntegerPlane := integerOverlayPlanes ![2,2,11,4]
def rev25_plane5 : IntegerPlane := ⟨(-2083356000000),(-746024000000),(-1117516707941)⟩
theorem rev25_plane5_mem : rev25_plane5 ∈ rev25_planes := by decide
def rev25_plane9 : IntegerPlane := ⟨(-2099728000000),1393416000000,(-740183860516)⟩
theorem rev25_plane9_mem : rev25_plane9 ∈ rev25_planes := by decide
def rev25_plane25 : IntegerPlane := ⟨2083356000000,(-746024000000),965839292059⟩
theorem rev25_plane25_mem : rev25_plane25 ∈ rev25_planes := by decide
def rev25_plane29 : IntegerPlane := ⟨2099728000000,1393416000000,1359544139484⟩
theorem rev25_plane29_mem : rev25_plane29 ∈ rev25_planes := by decide
def rev25_vertex0 : FractionPoint := fractionRow25[0]!
theorem rev25_vertex0_mem : rev25_vertex0∈fractionRow25 := by decide
def rev25_vertex1 : FractionPoint := fractionRow25[1]!
theorem rev25_vertex1_mem : rev25_vertex1∈fractionRow25 := by decide
def rev25_vertex2 : FractionPoint := fractionRow25[2]!
theorem rev25_vertex2_mem : rev25_vertex2∈fractionRow25 := by decide
def rev25_vertex3 : FractionPoint := fractionRow25[3]!
theorem rev25_vertex3_mem : rev25_vertex3∈fractionRow25 := by decide
def rev25_s0_ll : FractionPoint := ⟨52734014636747621,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev25_s0_ll_mem : rev25_s0_ll.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane5 rev25_vertex2 rev25_vertex3 rev25_s0_ll
    rev25_vertex2_mem rev25_vertex3_mem (by decide)
def rev25_s0_lr : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev25_s0_lr_mem : rev25_s0_lr.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane5 rev25_vertex2 rev25_vertex3 rev25_s0_lr
    rev25_vertex2_mem rev25_vertex3_mem (by decide)
def rev25_s0_ul : FractionPoint := ⟨52734014636747621,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev25_s0_ul_mem : rev25_s0_ul.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane9 rev25_vertex2 rev25_vertex1 rev25_s0_ul
    rev25_vertex2_mem rev25_vertex1_mem (by decide)
def rev25_s0_ur : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev25_s0_ur_mem : rev25_s0_ur.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane9 rev25_vertex2 rev25_vertex1 rev25_s0_ur
    rev25_vertex2_mem rev25_vertex1_mem (by decide)
theorem rev25_slab0 (p : Point) (hp : p∈IntegerCarrier rev25_planes)
    (hx0 : rev25_s0_ll.real.1≤p.1) (hx1 : p.1≤rev25_s0_lr.real.1) :
    p∈rationalHull (fractionRow25.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev25_plane5 rev25_plane9 rev25_s0_ll rev25_s0_lr rev25_s0_ul rev25_s0_ur
    (by decide) rev25_s0_ll_mem rev25_s0_lr_mem rev25_s0_ul_mem rev25_s0_ur_mem p
    (hp _ rev25_plane5_mem) (hp _ rev25_plane9_mem) hx0 hx1
def rev25_s1_ll : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev25_s1_ll_mem : rev25_s1_ll.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane25 rev25_vertex3 rev25_vertex0 rev25_s1_ll
    rev25_vertex3_mem rev25_vertex0_mem (by decide)
def rev25_s1_lr : FractionPoint := ⟨59001712002452379,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev25_s1_lr_mem : rev25_s1_lr.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane25 rev25_vertex3 rev25_vertex0 rev25_s1_lr
    rev25_vertex3_mem rev25_vertex0_mem (by decide)
def rev25_s1_ul : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev25_s1_ul_mem : rev25_s1_ul.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane29 rev25_vertex1 rev25_vertex0 rev25_s1_ul
    rev25_vertex1_mem rev25_vertex0_mem (by decide)
def rev25_s1_ur : FractionPoint := ⟨59001712002452379,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev25_s1_ur_mem : rev25_s1_ur.real ∈ rationalHull (fractionRow25.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow25 rev25_plane29 rev25_vertex1 rev25_vertex0 rev25_s1_ur
    rev25_vertex1_mem rev25_vertex0_mem (by decide)
theorem rev25_slab1 (p : Point) (hp : p∈IntegerCarrier rev25_planes)
    (hx0 : rev25_s1_ll.real.1≤p.1) (hx1 : p.1≤rev25_s1_lr.real.1) :
    p∈rationalHull (fractionRow25.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev25_plane25 rev25_plane29 rev25_s1_ll rev25_s1_lr rev25_s1_ul rev25_s1_ur
    (by decide) rev25_s1_ll_mem rev25_s1_lr_mem rev25_s1_ul_mem rev25_s1_ur_mem p
    (hp _ rev25_plane25_mem) (hp _ rev25_plane29_mem) hx0 hx1
theorem rev25_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev25_planes) : rev25_s0_ll.real.1≤p.1 := by
  have hc := rev25_plane5.combine_sound rev25_plane9 1393416000000 746024000000 (by decide) (by decide) p
    (hp _ rev25_plane5_mem) (hp _ rev25_plane9_mem)
  exact (rev25_plane5.combine rev25_plane9 1393416000000 746024000000).xBoundCheck_sound rev25_s0_ll.nx rev25_s0_ll.dx true (by decide) p hc
theorem rev25_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev25_planes) : p.1≤rev25_s1_lr.real.1 := by
  have hc := rev25_plane25.combine_sound rev25_plane29 1393416000000 746024000000 (by decide) (by decide) p
    (hp _ rev25_plane25_mem) (hp _ rev25_plane29_mem)
  exact (rev25_plane25.combine rev25_plane29 1393416000000 746024000000).xBoundCheck_sound rev25_s1_lr.nx rev25_s1_lr.dx false (by decide) p hc
theorem rev25_hull (p : Point) (hp : p∈IntegerCarrier rev25_planes) :
    p∈rationalHull (fractionRow25.map FractionPoint.rational) := by
  have hxlo := rev25_bound0_lo p hp
  have hxhi := rev25_bound0_hi p hp
  by_cases h0 : p.1≤rev25_s0_lr.real.1
  · exact rev25_slab0 p hp hxlo h0
  exact rev25_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull25 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,2,11,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow25 := by
  rw [← fractionRow25_correct]
  exact rev25_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull25
