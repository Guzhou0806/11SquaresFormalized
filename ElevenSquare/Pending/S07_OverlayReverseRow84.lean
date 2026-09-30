import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev84_planes : List IntegerPlane := integerOverlayPlanes ![6,9,6,6]
def rev84_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev84_plane13_mem : rev84_plane13 ∈ rev84_planes := by decide
def rev84_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev84_plane30_mem : rev84_plane30 ∈ rev84_planes := by decide
def rev84_plane53 : IntegerPlane := ⟨1343640000000,2164112000000,1753876000000⟩
theorem rev84_plane53_mem : rev84_plane53 ∈ rev84_planes := by decide
def rev84_plane73 : IntegerPlane := ⟨1343640000000,(-2164112000000),(-410236000000)⟩
theorem rev84_plane73_mem : rev84_plane73 ∈ rev84_planes := by decide
def rev84_vertex0 : FractionPoint := fractionRow84[0]!
theorem rev84_vertex0_mem : rev84_vertex0∈fractionRow84 := by decide
theorem rev84_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev84_planes) : rev84_vertex0.real.1≤p.1 := by
  have hc := rev84_plane13.combine_sound rev84_plane30 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev84_plane13_mem) (hp _ rev84_plane30_mem)
  exact (rev84_plane13.combine rev84_plane30 1343640000000 1343640000000).xBoundCheck_sound rev84_vertex0.nx rev84_vertex0.dx true (by decide) p hc
theorem rev84_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev84_planes) : p.1≤rev84_vertex0.real.1 := by
  have hc := rev84_plane53.combine_sound rev84_plane73 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev84_plane53_mem) (hp _ rev84_plane73_mem)
  exact (rev84_plane53.combine rev84_plane73 2164112000000 2164112000000).xBoundCheck_sound rev84_vertex0.nx rev84_vertex0.dx false (by decide) p hc
theorem rev84_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev84_planes) : rev84_vertex0.real.2≤p.2 := by
  have hc := rev84_plane13.combine_sound rev84_plane73 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev84_plane13_mem) (hp _ rev84_plane73_mem)
  exact (rev84_plane13.combine rev84_plane73 1343640000000 2164112000000).swap.xBoundCheck_sound rev84_vertex0.ny rev84_vertex0.dy true (by decide) (p.2,p.1)
    ((rev84_plane13.combine rev84_plane73 1343640000000 2164112000000).swap_contains p hc)
theorem rev84_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev84_planes) : p.2≤rev84_vertex0.real.2 := by
  have hc := rev84_plane13.combine_sound rev84_plane53 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev84_plane13_mem) (hp _ rev84_plane53_mem)
  exact (rev84_plane13.combine rev84_plane53 1343640000000 2164112000000).swap.xBoundCheck_sound rev84_vertex0.ny rev84_vertex0.dy false (by decide) (p.2,p.1)
    ((rev84_plane13.combine rev84_plane53 1343640000000 2164112000000).swap_contains p hc)
theorem rev84_hull (p : Point) (hp : p∈IntegerCarrier rev84_planes) :
    p∈rationalHull (fractionRow84.map FractionPoint.rational) := by
  have hxlo := rev84_bound0_lo p hp
  have hxhi := rev84_bound0_hi p hp
  have hylo := rev84_bound1_lo p hp
  have hyhi := rev84_bound1_hi p hp
  have he : p=rev84_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev84_vertex0.mem_rationalHull fractionRow84 rev84_vertex0_mem
theorem overlay_in_hull84 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,6,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow84 := by
  rw [← fractionRow84_correct]
  exact rev84_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull84
