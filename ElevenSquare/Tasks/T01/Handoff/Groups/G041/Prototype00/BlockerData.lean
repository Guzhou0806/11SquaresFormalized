import ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00.Cover
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell00
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell08
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicMajorityFieldRow

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.SharedFieldOwnership
noncomputable section

def point00 : QPoint :=
  (80206788320008528328995421/100000000000000000000000000,
   176483527032089485245355847/200000000000000000000000000)
def point08a : QPoint :=
  (40697655775523476432821091/50000000000000000000000000,
   120587362069840971382694247/50000000000000000000000000)
def point08b : QPoint :=
  (40447655775523476432821091/50000000000000000000000000,
   120587362069840971382694247/50000000000000000000000000)
def point08c : QPoint :=
  (40697655775523476432821091/50000000000000000000000000,
   120337362069840971382694247/50000000000000000000000000)

def rowCert : SymbolicFieldRowCertificate := {
  source := source
  targets := [.median target00,
    .blocker target01 point00 (49999/100000),
    .blocker target02 point08a (49999/100000),
    .blocker target03 point08b (49999/100000),
    .blocker target04 point08c (49999/100000)]
  cover := node000
}

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G041.Prototype00
