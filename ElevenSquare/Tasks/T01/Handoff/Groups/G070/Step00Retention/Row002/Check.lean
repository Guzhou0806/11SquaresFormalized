import ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row002.CorePolygon
import ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row002.Facets
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row002.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row002
noncomputable section

theorem retained_checked :
    RetainedCoreFreshCheck keptRow core corePolygon fresh witnesses := by
  refine ⟨core_polygon_checked, ?_, facets_match, facets_checked⟩
  intro v hv
  exact core_checked v hv

theorem fresh_sound (q : UnitSquare) (hq : keptRow.contains q)
    (p : QPoint) (hp : p ∈ fresh) : OpenSquare q (realPoint p) :=
  retained_core_fresh_sound keptRow core corePolygon fresh witnesses
    retained_checked q hq p hp

#print axioms retained_checked
#print axioms fresh_sound

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row002
