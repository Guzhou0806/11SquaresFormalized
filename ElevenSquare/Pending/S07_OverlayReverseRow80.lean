import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev80_planes : List IntegerPlane := integerOverlayPlanes ![6,6,6,6]
def rev80_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev80_plane13_mem : rev80_plane13 ∈ rev80_planes := by decide
def rev80_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev80_plane33_mem : rev80_plane33 ∈ rev80_planes := by decide
def rev80_plane73 : IntegerPlane := ⟨1343640000000,(-2164112000000),(-410236000000)⟩
theorem rev80_plane73_mem : rev80_plane73 ∈ rev80_planes := by decide
def rev80_vertex0 : FractionPoint := fractionRow80[0]!
theorem rev80_vertex0_mem : rev80_vertex0∈fractionRow80 := by decide
theorem rev80_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev80_planes) : rev80_vertex0.real.1≤p.1 := by
  have hc := rev80_plane13.combine_sound rev80_plane73 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev80_plane13_mem) (hp _ rev80_plane73_mem)
  exact (rev80_plane13.combine rev80_plane73 2164112000000 1343640000000).xBoundCheck_sound rev80_vertex0.nx rev80_vertex0.dx true (by decide) p hc
theorem rev80_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev80_planes) : p.1≤rev80_vertex0.real.1 := by
  have hc := rev80_plane33.combine_sound rev80_plane73 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev80_plane33_mem) (hp _ rev80_plane73_mem)
  exact (rev80_plane33.combine rev80_plane73 2164112000000 1343640000000).xBoundCheck_sound rev80_vertex0.nx rev80_vertex0.dx false (by decide) p hc
theorem rev80_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev80_planes) : rev80_vertex0.real.2≤p.2 := by
  have hc := rev80_plane13.combine_sound rev80_plane73 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev80_plane13_mem) (hp _ rev80_plane73_mem)
  exact (rev80_plane13.combine rev80_plane73 1343640000000 2164112000000).swap.xBoundCheck_sound rev80_vertex0.ny rev80_vertex0.dy true (by decide) (p.2,p.1)
    ((rev80_plane13.combine rev80_plane73 1343640000000 2164112000000).swap_contains p hc)
theorem rev80_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev80_planes) : p.2≤rev80_vertex0.real.2 := by
  have hc := rev80_plane13.combine_sound rev80_plane33 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev80_plane13_mem) (hp _ rev80_plane33_mem)
  exact (rev80_plane13.combine rev80_plane33 2164112000000 2164112000000).swap.xBoundCheck_sound rev80_vertex0.ny rev80_vertex0.dy false (by decide) (p.2,p.1)
    ((rev80_plane13.combine rev80_plane33 2164112000000 2164112000000).swap_contains p hc)
theorem rev80_hull (p : Point) (hp : p∈IntegerCarrier rev80_planes) :
    p∈rationalHull (fractionRow80.map FractionPoint.rational) := by
  have hxlo := rev80_bound0_lo p hp
  have hxhi := rev80_bound0_hi p hp
  have hylo := rev80_bound1_lo p hp
  have hyhi := rev80_bound1_hi p hp
  have he : p=rev80_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev80_vertex0.mem_rationalHull fractionRow80 rev80_vertex0_mem
theorem overlay_in_hull80 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,6,6,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow80 := by
  rw [← fractionRow80_correct]
  exact rev80_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull80
