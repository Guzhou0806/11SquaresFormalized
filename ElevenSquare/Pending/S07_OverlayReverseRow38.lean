import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev38_planes : List IntegerPlane := integerOverlayPlanes ![3,5,10,8]
def rev38_plane6 : IntegerPlane := ⟨(-1855520000000),287616000000,(-1356143759600)⟩
theorem rev38_plane6_mem : rev38_plane6 ∈ rev38_planes := by decide
def rev38_plane11 : IntegerPlane := ⟨202532000000,1861776000000,585903739447⟩
theorem rev38_plane11_mem : rev38_plane11 ∈ rev38_planes := by decide
def rev38_plane59 : IntegerPlane := ⟨1440116000000,(-2129316000000),612143880216⟩
theorem rev38_plane59_mem : rev38_plane59 ∈ rev38_planes := by decide
def rev38_vertex0 : FractionPoint := fractionRow38[0]!
theorem rev38_vertex0_mem : rev38_vertex0∈fractionRow38 := by decide
def rev38_vertex1 : FractionPoint := fractionRow38[1]!
theorem rev38_vertex1_mem : rev38_vertex1∈fractionRow38 := by decide
def rev38_vertex2 : FractionPoint := fractionRow38[2]!
theorem rev38_vertex2_mem : rev38_vertex2∈fractionRow38 := by decide
def rev38_s0_ll : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev38_s0_ll_mem : rev38_s0_ll.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane59 rev38_vertex2 rev38_vertex0 rev38_s0_ll
    rev38_vertex2_mem rev38_vertex0_mem (by decide)
def rev38_s0_lr : FractionPoint := ⟨1001990771613779,1306850464000000,32150121407915446907,139134880130131200000⟩
theorem rev38_s0_lr_mem : rev38_s0_lr.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane59 rev38_vertex2 rev38_vertex0 rev38_s0_lr
    rev38_vertex2_mem rev38_vertex0_mem (by decide)
def rev38_s0_ul : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev38_s0_ul_mem : rev38_s0_ul.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane6 rev38_vertex2 rev38_vertex1 rev38_s0_ul
    rev38_vertex2_mem rev38_vertex1_mem (by decide)
def rev38_s0_ur : FractionPoint := ⟨1001990771613779,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev38_s0_ur_mem : rev38_s0_ur.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane6 rev38_vertex2 rev38_vertex1 rev38_s0_ur
    rev38_vertex2_mem rev38_vertex1_mem (by decide)
theorem rev38_slab0 (p : Point) (hp : p∈IntegerCarrier rev38_planes)
    (hx0 : rev38_s0_ll.real.1≤p.1) (hx1 : p.1≤rev38_s0_lr.real.1) :
    p∈rationalHull (fractionRow38.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev38_plane59 rev38_plane6 rev38_s0_ll rev38_s0_lr rev38_s0_ul rev38_s0_ur
    (by decide) rev38_s0_ll_mem rev38_s0_lr_mem rev38_s0_ul_mem rev38_s0_ur_mem p
    (hp _ rev38_plane59_mem) (hp _ rev38_plane6_mem) hx0 hx1
def rev38_s1_ll : FractionPoint := ⟨1001990771613779,1306850464000000,32150121407915446907,139134880130131200000⟩
theorem rev38_s1_ll_mem : rev38_s1_ll.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane59 rev38_vertex2 rev38_vertex0 rev38_s1_ll
    rev38_vertex2_mem rev38_vertex0_mem (by decide)
def rev38_s1_lr : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev38_s1_lr_mem : rev38_s1_lr.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane59 rev38_vertex2 rev38_vertex0 rev38_s1_lr
    rev38_vertex2_mem rev38_vertex0_mem (by decide)
def rev38_s1_ul : FractionPoint := ⟨1001990771613779,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev38_s1_ul_mem : rev38_s1_ul.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane11 rev38_vertex1 rev38_vertex0 rev38_s1_ul
    rev38_vertex1_mem rev38_vertex0_mem (by decide)
def rev38_s1_ur : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev38_s1_ur_mem : rev38_s1_ur.real ∈ rationalHull (fractionRow38.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow38 rev38_plane11 rev38_vertex1 rev38_vertex0 rev38_s1_ur
    rev38_vertex1_mem rev38_vertex0_mem (by decide)
theorem rev38_slab1 (p : Point) (hp : p∈IntegerCarrier rev38_planes)
    (hx0 : rev38_s1_ll.real.1≤p.1) (hx1 : p.1≤rev38_s1_lr.real.1) :
    p∈rationalHull (fractionRow38.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev38_plane59 rev38_plane11 rev38_s1_ll rev38_s1_lr rev38_s1_ul rev38_s1_ur
    (by decide) rev38_s1_ll_mem rev38_s1_lr_mem rev38_s1_ul_mem rev38_s1_ur_mem p
    (hp _ rev38_plane59_mem) (hp _ rev38_plane11_mem) hx0 hx1
theorem rev38_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev38_planes) : rev38_s0_ll.real.1≤p.1 := by
  have hc := rev38_plane6.combine_sound rev38_plane59 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev38_plane6_mem) (hp _ rev38_plane59_mem)
  exact (rev38_plane6.combine rev38_plane59 2129316000000 287616000000).xBoundCheck_sound rev38_s0_ll.nx rev38_s0_ll.dx true (by decide) p hc
theorem rev38_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev38_planes) : p.1≤rev38_s1_lr.real.1 := by
  have hc := rev38_plane11.combine_sound rev38_plane59 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev38_plane11_mem) (hp _ rev38_plane59_mem)
  exact (rev38_plane11.combine rev38_plane59 2129316000000 1861776000000).xBoundCheck_sound rev38_s1_lr.nx rev38_s1_lr.dx false (by decide) p hc
theorem rev38_hull (p : Point) (hp : p∈IntegerCarrier rev38_planes) :
    p∈rationalHull (fractionRow38.map FractionPoint.rational) := by
  have hxlo := rev38_bound0_lo p hp
  have hxhi := rev38_bound0_hi p hp
  by_cases h0 : p.1≤rev38_s0_lr.real.1
  · exact rev38_slab0 p hp hxlo h0
  exact rev38_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull38 (p : Point)
    (hp : ∀ g, ClosedCell ((![3,5,10,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow38 := by
  rw [← fractionRow38_correct]
  exact rev38_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull38
