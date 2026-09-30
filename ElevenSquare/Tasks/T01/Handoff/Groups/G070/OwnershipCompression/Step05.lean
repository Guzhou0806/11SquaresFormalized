import ElevenSquare.Tasks.T01.FiniteOwnership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step05
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def owner : Owner := 6
def oldOwned : List QPoint := [
  ((191963927/125000000 : ℚ), (2175027803/1000000000 : ℚ)),
  ((1549306113/1000000000 : ℚ), (1082678421/500000000 : ℚ)),
  ((19625653/12500000 : ℚ), (545006253/250000000 : ℚ)),
  ((1548858441/1000000000 : ℚ), (274425403/125000000 : ℚ)),
  ((1538205531/1000000000 : ℚ), (546775057/250000000 : ℚ))
]
def fresh : List QPoint := [
  ((6213571958672675929094022517/4775000000000000000000000000 : ℚ), (47202319115325062702897778263/19100000000000000000000000000 : ℚ)),
  ((50795223334033256664890651731/38200000000000000000000000000 : ℚ), (86856388775695993746353756591/38200000000000000000000000000 : ℚ)),
  ((60156252460464148382673794003/38200000000000000000000000000 : ℚ), (80968179733356237371612500619/38200000000000000000000000000 : ℚ)),
  ((60657925365344996409458315067/38200000000000000000000000000 : ℚ), (20205532401702929739817953797/9550000000000000000000000000 : ℚ)),
  ((58993753144748733811689011837/38200000000000000000000000000 : ℚ), (68677495588587123492616147/30560000000000000000000000 : ℚ)),
  ((14048291753634772284750321463/9550000000000000000000000000 : ℚ), (44789638687672431609182677357/19100000000000000000000000000 : ℚ))
]
def output : List QPoint := [
  ((6213571958672675929094022517/4775000000000000000000000000 : ℚ), (47202319115325062702897778263/19100000000000000000000000000 : ℚ)),
  ((50795223334033256664890651731/38200000000000000000000000000 : ℚ), (86856388775695993746353756591/38200000000000000000000000000 : ℚ)),
  ((60156252460464148382673794003/38200000000000000000000000000 : ℚ), (80968179733356237371612500619/38200000000000000000000000000 : ℚ)),
  ((60657925365344996409458315067/38200000000000000000000000000 : ℚ), (20205532401702929739817953797/9550000000000000000000000000 : ℚ)),
  ((19625653/12500000 : ℚ), (545006253/250000000 : ℚ)),
  ((58993753144748733811689011837/38200000000000000000000000000 : ℚ), (68677495588587123492616147/30560000000000000000000000 : ℚ)),
  ((14048291753634772284750321463/9550000000000000000000000000 : ℚ), (44789638687672431609182677357/19100000000000000000000000000 : ℚ))
]
def witnesses : List HullWitness := [
  .vertex 5,
  .vertex 6,
  .vertex 7,
  .vertex 8,
  .vertex 2,
  .vertex 9,
  .vertex 10
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
end ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step05

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step05.compression_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step05.checked
