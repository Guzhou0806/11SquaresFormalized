import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell00Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell01Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell02Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell03Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell04Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell05Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell06Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell07Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell08Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell09Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell10Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell11Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell12Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell13Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell14Data
import ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.CellRoots.Cell15Data

namespace ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The same normalized initial wall geometry serves every archived generic
    group containing this physical cell. The caller chooses the owned points. -/
def rootForCell (cell : Fin 16) (owned : List QPoint) : CellRootCertificate 32 :=
  match cell.val with
  | 0 => CellRoots.Cell00Data.root owned
  | 1 => CellRoots.Cell01Data.root owned
  | 2 => CellRoots.Cell02Data.root owned
  | 3 => CellRoots.Cell03Data.root owned
  | 4 => CellRoots.Cell04Data.root owned
  | 5 => CellRoots.Cell05Data.root owned
  | 6 => CellRoots.Cell06Data.root owned
  | 7 => CellRoots.Cell07Data.root owned
  | 8 => CellRoots.Cell08Data.root owned
  | 9 => CellRoots.Cell09Data.root owned
  | 10 => CellRoots.Cell10Data.root owned
  | 11 => CellRoots.Cell11Data.root owned
  | 12 => CellRoots.Cell12Data.root owned
  | 13 => CellRoots.Cell13Data.root owned
  | 14 => CellRoots.Cell14Data.root owned
  | _ => CellRoots.Cell15Data.root owned

end
end ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots
