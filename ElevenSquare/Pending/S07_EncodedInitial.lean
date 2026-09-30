import ElevenSquare.Pending.S07_EncodedData
namespace ElevenSquare.Pending.EncodedSearch
open Propagation
def initialDomains (k : ℕ) : Domains :=
  (mask k).map (fun v => (v, (List.range 220).filter (fun r => decide (label r 0 = v))))
end ElevenSquare.Pending.EncodedSearch
