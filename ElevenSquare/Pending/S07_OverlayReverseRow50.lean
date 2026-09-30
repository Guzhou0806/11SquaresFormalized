import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev50_planes : List IntegerPlane := integerOverlayPlanes ![4,11,2,2]
def rev50_plane45 : IntegerPlane := ⟨(-746024000000),2083356000000,965839292059⟩
theorem rev50_plane45_mem : rev50_plane45 ∈ rev50_planes := by decide
def rev50_plane49 : IntegerPlane := ⟨1393416000000,2099728000000,1359544139484⟩
theorem rev50_plane49_mem : rev50_plane49 ∈ rev50_planes := by decide
def rev50_plane65 : IntegerPlane := ⟨(-746024000000),(-2083356000000),(-1117516707941)⟩
theorem rev50_plane65_mem : rev50_plane65 ∈ rev50_planes := by decide
def rev50_plane69 : IntegerPlane := ⟨1393416000000,(-2099728000000),(-740183860516)⟩
theorem rev50_plane69_mem : rev50_plane69 ∈ rev50_planes := by decide
def rev50_vertex0 : FractionPoint := fractionRow50[0]!
theorem rev50_vertex0_mem : rev50_vertex0∈fractionRow50 := by decide
def rev50_vertex1 : FractionPoint := fractionRow50[1]!
theorem rev50_vertex1_mem : rev50_vertex1∈fractionRow50 := by decide
def rev50_vertex2 : FractionPoint := fractionRow50[2]!
theorem rev50_vertex2_mem : rev50_vertex2∈fractionRow50 := by decide
def rev50_vertex3 : FractionPoint := fractionRow50[3]!
theorem rev50_vertex3_mem : rev50_vertex3∈fractionRow50 := by decide
def rev50_s0_ll : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev50_s0_ll_mem : rev50_s0_ll.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane65 rev50_vertex3 rev50_vertex0 rev50_s0_ll
    rev50_vertex3_mem rev50_vertex0_mem (by decide)
def rev50_s0_lr : FractionPoint := ⟨25137957350699011,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev50_s0_lr_mem : rev50_s0_lr.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane65 rev50_vertex3 rev50_vertex0 rev50_s0_lr
    rev50_vertex3_mem rev50_vertex0_mem (by decide)
def rev50_s0_ul : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev50_s0_ul_mem : rev50_s0_ul.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane45 rev50_vertex3 rev50_vertex2 rev50_s0_ul
    rev50_vertex3_mem rev50_vertex2_mem (by decide)
def rev50_s0_ur : FractionPoint := ⟨25137957350699011,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev50_s0_ur_mem : rev50_s0_ur.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane45 rev50_vertex3 rev50_vertex2 rev50_s0_ur
    rev50_vertex3_mem rev50_vertex2_mem (by decide)
theorem rev50_slab0 (p : Point) (hp : p∈IntegerCarrier rev50_planes)
    (hx0 : rev50_s0_ll.real.1≤p.1) (hx1 : p.1≤rev50_s0_lr.real.1) :
    p∈rationalHull (fractionRow50.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev50_plane65 rev50_plane45 rev50_s0_ll rev50_s0_lr rev50_s0_ul rev50_s0_ur
    (by decide) rev50_s0_ll_mem rev50_s0_lr_mem rev50_s0_ul_mem rev50_s0_ur_mem p
    (hp _ rev50_plane65_mem) (hp _ rev50_plane45_mem) hx0 hx1
def rev50_s1_ll : FractionPoint := ⟨25137957350699011,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev50_s1_ll_mem : rev50_s1_ll.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane69 rev50_vertex0 rev50_vertex1 rev50_s1_ll
    rev50_vertex0_mem rev50_vertex1_mem (by decide)
def rev50_s1_lr : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev50_s1_lr_mem : rev50_s1_lr.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane69 rev50_vertex0 rev50_vertex1 rev50_s1_lr
    rev50_vertex0_mem rev50_vertex1_mem (by decide)
def rev50_s1_ul : FractionPoint := ⟨25137957350699011,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev50_s1_ul_mem : rev50_s1_ul.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane49 rev50_vertex2 rev50_vertex1 rev50_s1_ul
    rev50_vertex2_mem rev50_vertex1_mem (by decide)
def rev50_s1_ur : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev50_s1_ur_mem : rev50_s1_ur.real ∈ rationalHull (fractionRow50.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow50 rev50_plane49 rev50_vertex2 rev50_vertex1 rev50_s1_ur
    rev50_vertex2_mem rev50_vertex1_mem (by decide)
theorem rev50_slab1 (p : Point) (hp : p∈IntegerCarrier rev50_planes)
    (hx0 : rev50_s1_ll.real.1≤p.1) (hx1 : p.1≤rev50_s1_lr.real.1) :
    p∈rationalHull (fractionRow50.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev50_plane69 rev50_plane49 rev50_s1_ll rev50_s1_lr rev50_s1_ul rev50_s1_ur
    (by decide) rev50_s1_ll_mem rev50_s1_lr_mem rev50_s1_ul_mem rev50_s1_ur_mem p
    (hp _ rev50_plane69_mem) (hp _ rev50_plane49_mem) hx0 hx1
theorem rev50_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev50_planes) : rev50_s0_ll.real.1≤p.1 := by
  have hc := rev50_plane45.combine_sound rev50_plane65 2083356000000 2083356000000 (by decide) (by decide) p
    (hp _ rev50_plane45_mem) (hp _ rev50_plane65_mem)
  exact (rev50_plane45.combine rev50_plane65 2083356000000 2083356000000).xBoundCheck_sound rev50_s0_ll.nx rev50_s0_ll.dx true (by decide) p hc
theorem rev50_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev50_planes) : p.1≤rev50_s1_lr.real.1 := by
  have hc := rev50_plane49.combine_sound rev50_plane69 2099728000000 2099728000000 (by decide) (by decide) p
    (hp _ rev50_plane49_mem) (hp _ rev50_plane69_mem)
  exact (rev50_plane49.combine rev50_plane69 2099728000000 2099728000000).xBoundCheck_sound rev50_s1_lr.nx rev50_s1_lr.dx false (by decide) p hc
theorem rev50_hull (p : Point) (hp : p∈IntegerCarrier rev50_planes) :
    p∈rationalHull (fractionRow50.map FractionPoint.rational) := by
  have hxlo := rev50_bound0_lo p hp
  have hxhi := rev50_bound0_hi p hp
  by_cases h0 : p.1≤rev50_s0_lr.real.1
  · exact rev50_slab0 p hp hxlo h0
  exact rev50_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull50 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,11,2,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow50 := by
  rw [← fractionRow50_correct]
  exact rev50_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull50
