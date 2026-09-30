import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev137_planes : List IntegerPlane := integerOverlayPlanes ![9,9,6,9]
def rev137_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev137_plane10_mem : rev137_plane10 ∈ rev137_planes := by decide
def rev137_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev137_plane30_mem : rev137_plane30 ∈ rev137_planes := by decide
def rev137_plane53 : IntegerPlane := ⟨1343640000000,2164112000000,1753876000000⟩
theorem rev137_plane53_mem : rev137_plane53 ∈ rev137_planes := by decide
def rev137_plane70 : IntegerPlane := ⟨(-1343640000000),2164112000000,410236000000⟩
theorem rev137_plane70_mem : rev137_plane70 ∈ rev137_planes := by decide
def rev137_vertex0 : FractionPoint := fractionRow137[0]!
theorem rev137_vertex0_mem : rev137_vertex0∈fractionRow137 := by decide
theorem rev137_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev137_planes) : rev137_vertex0.real.1≤p.1 := by
  have hc := rev137_plane30.combine_sound rev137_plane53 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev137_plane30_mem) (hp _ rev137_plane53_mem)
  exact (rev137_plane30.combine rev137_plane53 2164112000000 1343640000000).xBoundCheck_sound rev137_vertex0.nx rev137_vertex0.dx true (by decide) p hc
theorem rev137_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev137_planes) : p.1≤rev137_vertex0.real.1 := by
  have hc := rev137_plane10.combine_sound rev137_plane53 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev137_plane10_mem) (hp _ rev137_plane53_mem)
  exact (rev137_plane10.combine rev137_plane53 2164112000000 1343640000000).xBoundCheck_sound rev137_vertex0.nx rev137_vertex0.dx false (by decide) p hc
theorem rev137_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev137_planes) : rev137_vertex0.real.2≤p.2 := by
  have hc := rev137_plane10.combine_sound rev137_plane30 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev137_plane10_mem) (hp _ rev137_plane30_mem)
  exact (rev137_plane10.combine rev137_plane30 2164112000000 2164112000000).swap.xBoundCheck_sound rev137_vertex0.ny rev137_vertex0.dy true (by decide) (p.2,p.1)
    ((rev137_plane10.combine rev137_plane30 2164112000000 2164112000000).swap_contains p hc)
theorem rev137_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev137_planes) : p.2≤rev137_vertex0.real.2 := by
  have hc := rev137_plane10.combine_sound rev137_plane70 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev137_plane10_mem) (hp _ rev137_plane70_mem)
  exact (rev137_plane10.combine rev137_plane70 1343640000000 2164112000000).swap.xBoundCheck_sound rev137_vertex0.ny rev137_vertex0.dy false (by decide) (p.2,p.1)
    ((rev137_plane10.combine rev137_plane70 1343640000000 2164112000000).swap_contains p hc)
theorem rev137_hull (p : Point) (hp : p∈IntegerCarrier rev137_planes) :
    p∈rationalHull (fractionRow137.map FractionPoint.rational) := by
  have hxlo := rev137_bound0_lo p hp
  have hxhi := rev137_bound0_hi p hp
  have hylo := rev137_bound1_lo p hp
  have hyhi := rev137_bound1_hi p hp
  have he : p=rev137_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev137_vertex0.mem_rationalHull fractionRow137 rev137_vertex0_mem
theorem overlay_in_hull137 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,9,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow137 := by
  rw [← fractionRow137_correct]
  exact rev137_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull137
