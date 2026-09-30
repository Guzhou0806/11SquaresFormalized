import ElevenSquare.Tasks.T01.FiniteOwnership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step08
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def owner : Owner := 2
def oldOwned : List QPoint := [
  ((1439673887/500000000 : ℚ), (359788647/500000000 : ℚ)),
  ((1451239527/500000000 : ℚ), (706762123/1000000000 : ℚ)),
  ((3058261939/1000000000 : ℚ), (40587311/50000000 : ℚ)),
  ((1537998631/500000000 : ℚ), (830458721/1000000000 : ℚ)),
  ((3033327231/1000000000 : ℚ), (486019933/500000000 : ℚ)),
  ((1511413727/500000000 : ℚ), (497957757/500000000 : ℚ)),
  ((1439673887/500000000 : ℚ), (497957757/500000000 : ℚ))
]
def fresh : List QPoint := [
  ((13882805419345110502657363271/4775000000000000000000000000 : ℚ), (2040648280729888920547218429/9550000000000000000000000000 : ℚ)),
  ((27029384069321967777838393753/7640000000000000000000000000 : ℚ), (2520331918321563554443708097/9550000000000000000000000000 : ℚ)),
  ((27343197541348568371038371539/7640000000000000000000000000 : ℚ), (18000231747363592944507316557/38200000000000000000000000000 : ℚ)),
  ((67515722450628120194726774997/19100000000000000000000000000 : ℚ), (37664412783017022174968741019/38200000000000000000000000000 : ℚ))
]
def output : List QPoint := [
  ((1439673887/500000000 : ℚ), (359788647/500000000 : ℚ)),
  ((13882805419345110502657363271/4775000000000000000000000000 : ℚ), (2040648280729888920547218429/9550000000000000000000000000 : ℚ)),
  ((27029384069321967777838393753/7640000000000000000000000000 : ℚ), (2520331918321563554443708097/9550000000000000000000000000 : ℚ)),
  ((27343197541348568371038371539/7640000000000000000000000000 : ℚ), (18000231747363592944507316557/38200000000000000000000000000 : ℚ)),
  ((67515722450628120194726774997/19100000000000000000000000000 : ℚ), (37664412783017022174968741019/38200000000000000000000000000 : ℚ)),
  ((1511413727/500000000 : ℚ), (497957757/500000000 : ℚ)),
  ((1439673887/500000000 : ℚ), (497957757/500000000 : ℚ))
]
def witnesses : List HullWitness := [
  .vertex 0,
  .vertex 7,
  .vertex 8,
  .vertex 9,
  .vertex 10,
  .vertex 5,
  .vertex 6
]

/-- Exact convex compression only; strict ownership is checked per retained row. -/
theorem compression_checked :
    HullVerticesCheck (oldOwned ++ fresh) output witnesses := by
  norm_num [HullVerticesCheck, oldOwned, fresh, output, witnesses,
    HullWitness.Valid, HullWitness.eval, rationalMix]

def certificate (rows : List (PoseRow × List QPoint)) : OwnershipCertificate where
  fresh := fresh
  output := output
  rows := rows
  witnesses := witnesses

theorem checked (s : PoseState) (rows : List (PoseRow × List QPoint))
    (hold : s.owned owner = oldOwned)
    (hrows : rows.map Prod.fst = s.rows owner)
    (hpoints : ∀ item ∈ rows, ∀ p ∈ fresh, DirectPointCheck item.1 item.2 p) :
    (certificate rows).Check s owner := by
  refine ⟨hrows, hpoints, ?_⟩
  change HullVerticesCheck (s.owned owner ++ fresh) output witnesses
  rw [hold]
  exact compression_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step08

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step08.compression_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step08.checked
