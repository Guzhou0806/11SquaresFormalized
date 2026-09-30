import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev139_planes : List IntegerPlane := integerOverlayPlanes ![9,9,9,9]
def rev139_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev139_plane10_mem : rev139_plane10 ∈ rev139_planes := by decide
def rev139_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev139_plane30_mem : rev139_plane30 ∈ rev139_planes := by decide
def rev139_plane70 : IntegerPlane := ⟨(-1343640000000),2164112000000,410236000000⟩
theorem rev139_plane70_mem : rev139_plane70 ∈ rev139_planes := by decide
def rev139_vertex0 : FractionPoint := fractionRow139[0]!
theorem rev139_vertex0_mem : rev139_vertex0∈fractionRow139 := by decide
theorem rev139_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev139_planes) : rev139_vertex0.real.1≤p.1 := by
  have hc := rev139_plane30.combine_sound rev139_plane70 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev139_plane30_mem) (hp _ rev139_plane70_mem)
  exact (rev139_plane30.combine rev139_plane70 2164112000000 1343640000000).xBoundCheck_sound rev139_vertex0.nx rev139_vertex0.dx true (by decide) p hc
theorem rev139_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev139_planes) : p.1≤rev139_vertex0.real.1 := by
  have hc := rev139_plane10.combine_sound rev139_plane70 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev139_plane10_mem) (hp _ rev139_plane70_mem)
  exact (rev139_plane10.combine rev139_plane70 2164112000000 1343640000000).xBoundCheck_sound rev139_vertex0.nx rev139_vertex0.dx false (by decide) p hc
theorem rev139_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev139_planes) : rev139_vertex0.real.2≤p.2 := by
  have hc := rev139_plane10.combine_sound rev139_plane30 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev139_plane10_mem) (hp _ rev139_plane30_mem)
  exact (rev139_plane10.combine rev139_plane30 2164112000000 2164112000000).swap.xBoundCheck_sound rev139_vertex0.ny rev139_vertex0.dy true (by decide) (p.2,p.1)
    ((rev139_plane10.combine rev139_plane30 2164112000000 2164112000000).swap_contains p hc)
theorem rev139_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev139_planes) : p.2≤rev139_vertex0.real.2 := by
  have hc := rev139_plane10.combine_sound rev139_plane70 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev139_plane10_mem) (hp _ rev139_plane70_mem)
  exact (rev139_plane10.combine rev139_plane70 1343640000000 2164112000000).swap.xBoundCheck_sound rev139_vertex0.ny rev139_vertex0.dy false (by decide) (p.2,p.1)
    ((rev139_plane10.combine rev139_plane70 1343640000000 2164112000000).swap_contains p hc)
theorem rev139_hull (p : Point) (hp : p∈IntegerCarrier rev139_planes) :
    p∈rationalHull (fractionRow139.map FractionPoint.rational) := by
  have hxlo := rev139_bound0_lo p hp
  have hxhi := rev139_bound0_hi p hp
  have hylo := rev139_bound1_lo p hp
  have hyhi := rev139_bound1_hi p hp
  have he : p=rev139_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev139_vertex0.mem_rationalHull fractionRow139 rev139_vertex0_mem
theorem overlay_in_hull139 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,9,9,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow139 := by
  rw [← fractionRow139_correct]
  exact rev139_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull139
