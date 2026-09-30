import ElevenSquare.Tasks.T01.Handoff.Groups.G059.Root

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- The archived trace indexes physical cells. In the sorted owner order for
mask 1705, physical cell 5 is logical owner 4. -/
def finalCell : Fin 16 := ⟨5, by decide⟩
def finalOwner : Owner := ⟨4, by decide⟩

/-- The 32 exact intervals of `final_state.cells["5"]` in the archived
`mask1705-generic-v2.json` (SHA256
`4817703d50989fb9158022eff60ebf26c0cd7fbb3ad95ec999711881a9282c5d`).
Every corresponding `residual_polygons` list is
empty. The rows of a state are the flattened residual polygons. -/
def archivedFinalCell5 : List (ℚ × ℚ × List Polygon) := [
  (0, 1/32, []),
  (1/32, 1/16, []),
  (1/16, 3/32, []),
  (3/32, 1/8, []),
  (1/8, 5/32, []),
  (5/32, 3/16, []),
  (3/16, 7/32, []),
  (7/32, 1/4, []),
  (1/4, 9/32, []),
  (9/32, 5/16, []),
  (5/16, 11/32, []),
  (11/32, 3/8, []),
  (3/8, 13/32, []),
  (13/32, 7/16, []),
  (7/16, 15/32, []),
  (15/32, 1/2, []),
  (1/2, 17/32, []),
  (17/32, 9/16, []),
  (9/16, 19/32, []),
  (19/32, 5/8, []),
  (5/8, 21/32, []),
  (21/32, 11/16, []),
  (11/16, 23/32, []),
  (23/32, 3/4, []),
  (3/4, 25/32, []),
  (25/32, 13/16, []),
  (13/16, 27/32, []),
  (27/32, 7/8, []),
  (7/8, 29/32, []),
  (29/32, 15/16, []),
  (15/16, 31/32, []),
  (31/32, 1, [])
]

def archivedFinalCell5Rows : List PoseRow :=
  archivedFinalCell5.flatMap fun datum =>
    datum.2.2.map (fun poly => ⟨datum.1, datum.2.1, poly⟩)

/-- The nine points of `final_state.groups["5"]`, each divided by the
archived square side B so they inhabit Lean’s unit-square coordinates.
Their validity as owned points depends on the earlier checked program. -/
def archivedFinalCell5Owned : List QPoint := [
  (56478275722790237822876713591/38200000000000000000000000000, 27977135602069608694356152329/19100000000000000000000000000),
  (28280595710077412364577041491/19100000000000000000000000000, 2764810729091068157148015691/1910000000000000000000000000),
  (29644045819097145403497471881/19100000000000000000000000000, 26181268156920887153737653943/19100000000000000000000000000),
  (34020764518865891616460398809/19100000000000000000000000000, 45369775234831443344724762739/38200000000000000000000000000),
  (73542328644214048948904124191/38200000000000000000000000000, 11860449606701308221680111153/9550000000000000000000000000),
  (18557626873016966861210972403/9550000000000000000000000000, 24690321704876689879722055127/19100000000000000000000000000),
  (4524770176862434401981939781/2387500000000000000000000000, 26888244269144213259653271437/19100000000000000000000000000),
  (71716608430838869743683174267/38200000000000000000000000000, 55051883487936638409476161737/38200000000000000000000000000),
  (12386619476537356397562547721/7640000000000000000000000000, 2874228231335256009734387587/1910000000000000000000000000)
]

theorem archived_final_cell5_count : archivedFinalCell5.length = 32 := by
  decide

theorem archived_final_cell5_rows_empty : archivedFinalCell5Rows = [] := by
  simp [archivedFinalCell5Rows, archivedFinalCell5]

theorem archived_final_cell5_owned_count : archivedFinalCell5Owned.length = 9 := by
  decide

/-- The exact terminal consequence once the checked twelve-step program has
been linked to the archived final state's cell-5 projection. This premise is
an equality of actual state data, not a numerical audit flag. -/
theorem terminal_of_archived_final_cell5 (s : PoseState)
    (hrows : s.rows finalOwner = archivedFinalCell5Rows) :
    (TerminalCertificate.empty finalOwner).Check s := by
  simpa only [TerminalCertificate.Check, archived_final_cell5_rows_empty] using hrows

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.archived_final_cell5_rows_empty
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.terminal_of_archived_final_cell5
