import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev135_planes : List IntegerPlane := integerOverlayPlanes ![9,6,9,9]
def rev135_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev135_plane10_mem : rev135_plane10 ∈ rev135_planes := by decide
def rev135_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev135_plane33_mem : rev135_plane33 ∈ rev135_planes := by decide
def rev135_plane50 : IntegerPlane := ⟨(-1343640000000),(-2164112000000),(-1753876000000)⟩
theorem rev135_plane50_mem : rev135_plane50 ∈ rev135_planes := by decide
def rev135_plane70 : IntegerPlane := ⟨(-1343640000000),2164112000000,410236000000⟩
theorem rev135_plane70_mem : rev135_plane70 ∈ rev135_planes := by decide
def rev135_vertex0 : FractionPoint := fractionRow135[0]!
theorem rev135_vertex0_mem : rev135_vertex0∈fractionRow135 := by decide
theorem rev135_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev135_planes) : rev135_vertex0.real.1≤p.1 := by
  have hc := rev135_plane50.combine_sound rev135_plane70 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev135_plane50_mem) (hp _ rev135_plane70_mem)
  exact (rev135_plane50.combine rev135_plane70 2164112000000 2164112000000).xBoundCheck_sound rev135_vertex0.nx rev135_vertex0.dx true (by decide) p hc
theorem rev135_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev135_planes) : p.1≤rev135_vertex0.real.1 := by
  have hc := rev135_plane10.combine_sound rev135_plane33 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev135_plane10_mem) (hp _ rev135_plane33_mem)
  exact (rev135_plane10.combine rev135_plane33 1343640000000 1343640000000).xBoundCheck_sound rev135_vertex0.nx rev135_vertex0.dx false (by decide) p hc
theorem rev135_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev135_planes) : rev135_vertex0.real.2≤p.2 := by
  have hc := rev135_plane10.combine_sound rev135_plane50 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev135_plane10_mem) (hp _ rev135_plane50_mem)
  exact (rev135_plane10.combine rev135_plane50 1343640000000 2164112000000).swap.xBoundCheck_sound rev135_vertex0.ny rev135_vertex0.dy true (by decide) (p.2,p.1)
    ((rev135_plane10.combine rev135_plane50 1343640000000 2164112000000).swap_contains p hc)
theorem rev135_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev135_planes) : p.2≤rev135_vertex0.real.2 := by
  have hc := rev135_plane10.combine_sound rev135_plane70 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev135_plane10_mem) (hp _ rev135_plane70_mem)
  exact (rev135_plane10.combine rev135_plane70 1343640000000 2164112000000).swap.xBoundCheck_sound rev135_vertex0.ny rev135_vertex0.dy false (by decide) (p.2,p.1)
    ((rev135_plane10.combine rev135_plane70 1343640000000 2164112000000).swap_contains p hc)
theorem rev135_hull (p : Point) (hp : p∈IntegerCarrier rev135_planes) :
    p∈rationalHull (fractionRow135.map FractionPoint.rational) := by
  have hxlo := rev135_bound0_lo p hp
  have hxhi := rev135_bound0_hi p hp
  have hylo := rev135_bound1_lo p hp
  have hyhi := rev135_bound1_hi p hp
  have he : p=rev135_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev135_vertex0.mem_rationalHull fractionRow135 rev135_vertex0_mem
theorem overlay_in_hull135 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,9,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow135 := by
  rw [← fractionRow135_correct]
  exact rev135_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull135
