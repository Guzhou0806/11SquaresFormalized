import ElevenSquare.Pending.S05_Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! Raw rational field-coordinate vertices and the owner-9 witness from
`far15y-self-300.json`, step 7, row 220. These values are not physical
unit-square coordinates; use `Far15Scaled` for geometric collision. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def far15Row220Vertices : List QPoint :=
  [ (2687581/5000000, 25016227/10000000),
    (2687581/5000000, 250307569/100000000),
    (5348041/10000000, 250578779/100000000),
    (53480409/100000000, 125289389/50000000),
    (53480409/100000000, 250164183/100000000),
    (53482323/100000000, 250162269/100000000),
    (53751619/100000000, 250162269/100000000) ]

def far15Owner9Witness : QPoint :=
  (45936839/50000000, 103898071/50000000)


end
end ElevenSquare.Tasks.T07
