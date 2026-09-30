import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev129_planes : List IntegerPlane := integerOverlayPlanes ![9,6,5,5]
def rev129_plane8 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-1212544726896)⟩
theorem rev129_plane8_mem : rev129_plane8 ∈ rev129_planes := by decide
def rev129_plane35 : IntegerPlane := ⟨(-2093220000000),1468788000000,256243273104⟩
theorem rev129_plane35_mem : rev129_plane35 ∈ rev129_planes := by decide
def rev129_plane46 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-1359544139484)⟩
theorem rev129_plane46_mem : rev129_plane46 ∈ rev129_planes := by decide
def rev129_plane50 : IntegerPlane := ⟨824716000000,(-2112812000000),(-749041164456)⟩
theorem rev129_plane50_mem : rev129_plane50 ∈ rev129_planes := by decide
def rev129_plane66 : IntegerPlane := ⟨(-1393416000000),2099728000000,740183860516⟩
theorem rev129_plane66_mem : rev129_plane66 ∈ rev129_planes := by decide
def rev129_plane70 : IntegerPlane := ⟨824716000000,2112812000000,1363770835544⟩
theorem rev129_plane70_mem : rev129_plane70 ∈ rev129_planes := by decide
def rev129_vertex0 : FractionPoint := fractionRow129[0]!
theorem rev129_vertex0_mem : rev129_vertex0∈fractionRow129 := by decide
def rev129_vertex1 : FractionPoint := fractionRow129[1]!
theorem rev129_vertex1_mem : rev129_vertex1∈fractionRow129 := by decide
def rev129_vertex2 : FractionPoint := fractionRow129[2]!
theorem rev129_vertex2_mem : rev129_vertex2∈fractionRow129 := by decide
def rev129_vertex3 : FractionPoint := fractionRow129[3]!
theorem rev129_vertex3_mem : rev129_vertex3∈fractionRow129 := by decide
def rev129_vertex4 : FractionPoint := fractionRow129[4]!
theorem rev129_vertex4_mem : rev129_vertex4∈fractionRow129 := by decide
def rev129_vertex5 : FractionPoint := fractionRow129[5]!
theorem rev129_vertex5_mem : rev129_vertex5∈fractionRow129 := by decide
def rev129_s0_ll : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev129_s0_ll_mem : rev129_s0_ll.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane8 rev129_vertex0 rev129_vertex1 rev129_s0_ll
    rev129_vertex0_mem rev129_vertex1_mem (by decide)
def rev129_s0_lr : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev129_s0_lr_mem : rev129_s0_lr.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane8 rev129_vertex0 rev129_vertex1 rev129_s0_lr
    rev129_vertex0_mem rev129_vertex1_mem (by decide)
def rev129_s0_ul : FractionPoint := ⟨3320491159,14536250000,1,2⟩
theorem rev129_s0_ul_mem : rev129_s0_ul.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane35 rev129_vertex0 rev129_vertex5 rev129_s0_ul
    rev129_vertex0_mem rev129_vertex5_mem (by decide)
def rev129_s0_ur : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev129_s0_ur_mem : rev129_s0_ur.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane35 rev129_vertex0 rev129_vertex5 rev129_s0_ur
    rev129_vertex0_mem rev129_vertex5_mem (by decide)
theorem rev129_slab0 (p : Point) (hp : p∈IntegerCarrier rev129_planes)
    (hx0 : rev129_s0_ll.real.1≤p.1) (hx1 : p.1≤rev129_s0_lr.real.1) :
    p∈rationalHull (fractionRow129.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev129_plane8 rev129_plane35 rev129_s0_ll rev129_s0_lr rev129_s0_ul rev129_s0_ur
    (by decide) rev129_s0_ll_mem rev129_s0_lr_mem rev129_s0_ul_mem rev129_s0_ur_mem p
    (hp _ rev129_plane8_mem) (hp _ rev129_plane35_mem) hx0 hx1
def rev129_s1_ll : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev129_s1_ll_mem : rev129_s1_ll.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane46 rev129_vertex1 rev129_vertex2 rev129_s1_ll
    rev129_vertex1_mem rev129_vertex2_mem (by decide)
def rev129_s1_lr : FractionPoint := ⟨16245980828382513,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev129_s1_lr_mem : rev129_s1_lr.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane46 rev129_vertex1 rev129_vertex2 rev129_s1_lr
    rev129_vertex1_mem rev129_vertex2_mem (by decide)
def rev129_s1_ul : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev129_s1_ul_mem : rev129_s1_ul.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane66 rev129_vertex5 rev129_vertex4 rev129_s1_ul
    rev129_vertex5_mem rev129_vertex4_mem (by decide)
def rev129_s1_ur : FractionPoint := ⟨16245980828382513,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev129_s1_ur_mem : rev129_s1_ur.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane66 rev129_vertex5 rev129_vertex4 rev129_s1_ur
    rev129_vertex5_mem rev129_vertex4_mem (by decide)
theorem rev129_slab1 (p : Point) (hp : p∈IntegerCarrier rev129_planes)
    (hx0 : rev129_s1_ll.real.1≤p.1) (hx1 : p.1≤rev129_s1_lr.real.1) :
    p∈rationalHull (fractionRow129.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev129_plane46 rev129_plane66 rev129_s1_ll rev129_s1_lr rev129_s1_ul rev129_s1_ur
    (by decide) rev129_s1_ll_mem rev129_s1_lr_mem rev129_s1_ul_mem rev129_s1_ur_mem p
    (hp _ rev129_plane46_mem) (hp _ rev129_plane66_mem) hx0 hx1
def rev129_s2_ll : FractionPoint := ⟨16245980828382513,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev129_s2_ll_mem : rev129_s2_ll.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane50 rev129_vertex2 rev129_vertex3 rev129_s2_ll
    rev129_vertex2_mem rev129_vertex3_mem (by decide)
def rev129_s2_lr : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev129_s2_lr_mem : rev129_s2_lr.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane50 rev129_vertex2 rev129_vertex3 rev129_s2_lr
    rev129_vertex2_mem rev129_vertex3_mem (by decide)
def rev129_s2_ul : FractionPoint := ⟨16245980828382513,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev129_s2_ul_mem : rev129_s2_ul.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane70 rev129_vertex4 rev129_vertex3 rev129_s2_ul
    rev129_vertex4_mem rev129_vertex3_mem (by decide)
def rev129_s2_ur : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev129_s2_ur_mem : rev129_s2_ur.real ∈ rationalHull (fractionRow129.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow129 rev129_plane70 rev129_vertex4 rev129_vertex3 rev129_s2_ur
    rev129_vertex4_mem rev129_vertex3_mem (by decide)
theorem rev129_slab2 (p : Point) (hp : p∈IntegerCarrier rev129_planes)
    (hx0 : rev129_s2_ll.real.1≤p.1) (hx1 : p.1≤rev129_s2_lr.real.1) :
    p∈rationalHull (fractionRow129.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev129_plane50 rev129_plane70 rev129_s2_ll rev129_s2_lr rev129_s2_ul rev129_s2_ur
    (by decide) rev129_s2_ll_mem rev129_s2_lr_mem rev129_s2_ul_mem rev129_s2_ur_mem p
    (hp _ rev129_plane50_mem) (hp _ rev129_plane70_mem) hx0 hx1
theorem rev129_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev129_planes) : rev129_s0_ll.real.1≤p.1 := by
  have hc := rev129_plane8.combine_sound rev129_plane35 1468788000000 1468788000000 (by decide) (by decide) p
    (hp _ rev129_plane8_mem) (hp _ rev129_plane35_mem)
  exact (rev129_plane8.combine rev129_plane35 1468788000000 1468788000000).xBoundCheck_sound rev129_s0_ll.nx rev129_s0_ll.dx true (by decide) p hc
theorem rev129_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev129_planes) : p.1≤rev129_s2_lr.real.1 := by
  have hc := rev129_plane50.combine_sound rev129_plane70 2112812000000 2112812000000 (by decide) (by decide) p
    (hp _ rev129_plane50_mem) (hp _ rev129_plane70_mem)
  exact (rev129_plane50.combine rev129_plane70 2112812000000 2112812000000).xBoundCheck_sound rev129_s2_lr.nx rev129_s2_lr.dx false (by decide) p hc
theorem rev129_hull (p : Point) (hp : p∈IntegerCarrier rev129_planes) :
    p∈rationalHull (fractionRow129.map FractionPoint.rational) := by
  have hxlo := rev129_bound0_lo p hp
  have hxhi := rev129_bound0_hi p hp
  by_cases h0 : p.1≤rev129_s0_lr.real.1
  · exact rev129_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev129_s1_lr.real.1
  · exact rev129_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev129_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull129 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,5,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow129 := by
  rw [← fractionRow129_correct]
  exact rev129_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull129
