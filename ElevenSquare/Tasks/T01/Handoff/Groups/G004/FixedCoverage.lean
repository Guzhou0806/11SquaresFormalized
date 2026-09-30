import ElevenSquare.Tasks.T01.ClosedWindowCover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004
noncomputable section

def fixedCell01Windows : List (ℚ × ℚ) := [(0, 1/64), (1/64, 1/32), (1/32, 1/16), (1/16, 3/32), (3/32, 1/8), (1/8, 3/16), (3/16, 1/4), (1/4, 3/8), (3/8, 7/16), (7/16, 1/2), (1/2, 9/16), (9/16, 5/8), (5/8, 21/32), (21/32, 11/16), (11/16, 23/32), (23/32, 3/4), (3/4, 49/64), (49/64, 25/32), (25/32, 51/64), (51/64, 13/16), (13/16, 27/32), (27/32, 7/8), (7/8, 57/64), (57/64, 29/32), (29/32, 59/64), (59/64, 15/16), (15/16, 61/64), (61/64, 123/128), (123/128, 31/32), (31/32, 125/128), (125/128, 63/64), (63/64, 127/128), (127/128, 1)]

theorem fixedCell01_windows_checked :
    ClosedWindowCoverCheck fixedCell01Windows := by
  norm_num [fixedCell01Windows, ClosedWindowCoverCheck, ClosedWindowChain]

def fixedCell02Windows : List (ℚ × ℚ) := [(0, 1/256), (1/256, 1/128), (1/128, 3/256), (3/256, 1/64), (1/64, 3/128), (3/128, 1/32), (1/32, 5/128), (5/128, 3/64), (3/64, 1/16), (1/16, 5/64), (5/64, 3/32), (3/32, 1/8), (1/8, 5/32), (5/32, 3/16), (3/16, 1/4), (1/4, 3/8), (3/8, 1/2), (1/2, 5/8), (5/8, 3/4), (3/4, 7/8), (7/8, 15/16), (15/16, 31/32), (31/32, 1)]

theorem fixedCell02_windows_checked :
    ClosedWindowCoverCheck fixedCell02Windows := by
  norm_num [fixedCell02Windows, ClosedWindowCoverCheck, ClosedWindowChain]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004
