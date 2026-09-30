import ElevenSquare.Tasks.T01.ClosedWindowCover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
noncomputable section

def fixedCell05Windows : List (ℚ × ℚ) := [(0, 1/8), (1/8, 5/32), (5/32, 3/16), (3/16, 7/32), (7/32, 1/4), (1/4, 9/32), (9/32, 5/16), (5/16, 3/8), (3/8, 7/16), (7/16, 1/2), (1/2, 5/8), (5/8, 3/4), (3/4, 7/8), (7/8, 1)]

theorem fixedCell05_windows_checked :
    ClosedWindowCoverCheck fixedCell05Windows := by
  norm_num [fixedCell05Windows, ClosedWindowCoverCheck, ClosedWindowChain]

def fixedCell09Windows : List (ℚ × ℚ) := [(0, 1/16), (1/16, 1/8), (1/8, 1/4), (1/4, 5/16), (5/16, 11/32), (11/32, 3/8), (3/8, 13/32), (13/32, 7/16), (7/16, 15/32), (15/32, 1/2), (1/2, 33/64), (33/64, 17/32), (17/32, 35/64), (35/64, 9/16), (9/16, 37/64), (37/64, 19/32), (19/32, 5/8), (5/8, 21/32), (21/32, 11/16), (11/16, 3/4), (3/4, 13/16), (13/16, 7/8), (7/8, 29/32), (29/32, 15/16), (15/16, 31/32), (31/32, 1)]

theorem fixedCell09_windows_checked :
    ClosedWindowCoverCheck fixedCell09Windows := by
  norm_num [fixedCell09Windows, ClosedWindowCoverCheck, ClosedWindowChain]

def fixedCell10Windows : List (ℚ × ℚ) := [(0, 1/16), (1/16, 1/8), (1/8, 1/4), (1/4, 5/16), (5/16, 11/32), (11/32, 3/8), (3/8, 13/32), (13/32, 7/16), (7/16, 1/2), (1/2, 5/8), (5/8, 11/16), (11/16, 3/4), (3/4, 25/32), (25/32, 13/16), (13/16, 27/32), (27/32, 7/8), (7/8, 29/32), (29/32, 15/16), (15/16, 31/32), (31/32, 1)]

theorem fixedCell10_windows_checked :
    ClosedWindowCoverCheck fixedCell10Windows := by
  norm_num [fixedCell10Windows, ClosedWindowCoverCheck, ClosedWindowChain]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007
