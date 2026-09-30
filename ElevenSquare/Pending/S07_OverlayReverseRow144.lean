import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev144_planes : List IntegerPlane := integerOverlayPlanes ![9,11,5,5]
def rev144_plane8 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-1212544726896)⟩
theorem rev144_plane8_mem : rev144_plane8 ∈ rev144_planes := by decide
def rev144_plane30 : IntegerPlane := ⟨2093220000000,(-1468788000000),(-256243273104)⟩
theorem rev144_plane30_mem : rev144_plane30 ∈ rev144_planes := by decide
def rev144_plane66 : IntegerPlane := ⟨(-1393416000000),2099728000000,740183860516⟩
theorem rev144_plane66_mem : rev144_plane66 ∈ rev144_planes := by decide
def rev144_vertex0 : FractionPoint := fractionRow144[0]!
theorem rev144_vertex0_mem : rev144_vertex0∈fractionRow144 := by decide
def rev144_vertex1 : FractionPoint := fractionRow144[1]!
theorem rev144_vertex1_mem : rev144_vertex1∈fractionRow144 := by decide
def rev144_vertex2 : FractionPoint := fractionRow144[2]!
theorem rev144_vertex2_mem : rev144_vertex2∈fractionRow144 := by decide
def rev144_s0_ll : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev144_s0_ll_mem : rev144_s0_ll.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane8 rev144_vertex0 rev144_vertex1 rev144_s0_ll
    rev144_vertex0_mem rev144_vertex1_mem (by decide)
def rev144_s0_lr : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev144_s0_lr_mem : rev144_s0_lr.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane8 rev144_vertex0 rev144_vertex1 rev144_s0_lr
    rev144_vertex0_mem rev144_vertex1_mem (by decide)
def rev144_s0_ul : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev144_s0_ul_mem : rev144_s0_ul.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane66 rev144_vertex0 rev144_vertex2 rev144_s0_ul
    rev144_vertex0_mem rev144_vertex2_mem (by decide)
def rev144_s0_ur : FractionPoint := ⟨3320491159,14536250000,15386323151234849,30522171140000000⟩
theorem rev144_s0_ur_mem : rev144_s0_ur.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane66 rev144_vertex0 rev144_vertex2 rev144_s0_ur
    rev144_vertex0_mem rev144_vertex2_mem (by decide)
theorem rev144_slab0 (p : Point) (hp : p∈IntegerCarrier rev144_planes)
    (hx0 : rev144_s0_ll.real.1≤p.1) (hx1 : p.1≤rev144_s0_lr.real.1) :
    p∈rationalHull (fractionRow144.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev144_plane8 rev144_plane66 rev144_s0_ll rev144_s0_lr rev144_s0_ul rev144_s0_ur
    (by decide) rev144_s0_ll_mem rev144_s0_lr_mem rev144_s0_ul_mem rev144_s0_ur_mem p
    (hp _ rev144_plane8_mem) (hp _ rev144_plane66_mem) hx0 hx1
def rev144_s1_ll : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev144_s1_ll_mem : rev144_s1_ll.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane30 rev144_vertex1 rev144_vertex2 rev144_s1_ll
    rev144_vertex1_mem rev144_vertex2_mem (by decide)
def rev144_s1_lr : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev144_s1_lr_mem : rev144_s1_lr.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane30 rev144_vertex1 rev144_vertex2 rev144_s1_lr
    rev144_vertex1_mem rev144_vertex2_mem (by decide)
def rev144_s1_ul : FractionPoint := ⟨3320491159,14536250000,15386323151234849,30522171140000000⟩
theorem rev144_s1_ul_mem : rev144_s1_ul.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane66 rev144_vertex0 rev144_vertex2 rev144_s1_ul
    rev144_vertex0_mem rev144_vertex2_mem (by decide)
def rev144_s1_ur : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev144_s1_ur_mem : rev144_s1_ur.real ∈ rationalHull (fractionRow144.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow144 rev144_plane66 rev144_vertex0 rev144_vertex2 rev144_s1_ur
    rev144_vertex0_mem rev144_vertex2_mem (by decide)
theorem rev144_slab1 (p : Point) (hp : p∈IntegerCarrier rev144_planes)
    (hx0 : rev144_s1_ll.real.1≤p.1) (hx1 : p.1≤rev144_s1_lr.real.1) :
    p∈rationalHull (fractionRow144.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev144_plane30 rev144_plane66 rev144_s1_ll rev144_s1_lr rev144_s1_ul rev144_s1_ur
    (by decide) rev144_s1_ll_mem rev144_s1_lr_mem rev144_s1_ul_mem rev144_s1_ur_mem p
    (hp _ rev144_plane30_mem) (hp _ rev144_plane66_mem) hx0 hx1
theorem rev144_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev144_planes) : rev144_s0_ll.real.1≤p.1 := by
  have hc := rev144_plane8.combine_sound rev144_plane66 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev144_plane8_mem) (hp _ rev144_plane66_mem)
  exact (rev144_plane8.combine rev144_plane66 2099728000000 1468788000000).xBoundCheck_sound rev144_s0_ll.nx rev144_s0_ll.dx true (by decide) p hc
theorem rev144_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev144_planes) : p.1≤rev144_s1_lr.real.1 := by
  have hc := rev144_plane30.combine_sound rev144_plane66 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev144_plane30_mem) (hp _ rev144_plane66_mem)
  exact (rev144_plane30.combine rev144_plane66 2099728000000 1468788000000).xBoundCheck_sound rev144_s1_lr.nx rev144_s1_lr.dx false (by decide) p hc
theorem rev144_hull (p : Point) (hp : p∈IntegerCarrier rev144_planes) :
    p∈rationalHull (fractionRow144.map FractionPoint.rational) := by
  have hxlo := rev144_bound0_lo p hp
  have hxhi := rev144_bound0_hi p hp
  by_cases h0 : p.1≤rev144_s0_lr.real.1
  · exact rev144_slab0 p hp hxlo h0
  exact rev144_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull144 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,11,5,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow144 := by
  rw [← fractionRow144_correct]
  exact rev144_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull144
