import ElevenSquare.Tasks.T01.ClosedWindowCover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005
noncomputable section

def fixedCell02Windows : List (ℚ × ℚ) := [
  (0, 1/16), (1/16, 1/8), (1/8, 3/16), (3/16, 7/32), (7/32, 15/64), (15/64, 1/4), (1/4, 65/256), (65/256, 33/128), (33/128, 67/256), (67/256, 17/64), (17/64, 69/256), (69/256, 35/128), (35/128, 71/256), (71/256, 9/32), (9/32, 73/256), (73/256, 37/128), (37/128, 19/64), (19/64, 39/128), (39/128, 5/16), (5/16, 41/128), (41/128, 21/64), (21/64, 43/128), (43/128, 11/32), (11/32, 45/128), (45/128, 23/64), (23/64, 3/8), (3/8, 25/64), (25/64, 13/32), (13/32, 27/64), (27/64, 7/16), (7/16, 15/32), (15/32, 1/2), (1/2, 9/16), (9/16, 5/8), (5/8, 11/16), (11/16, 3/4), (3/4, 13/16), (13/16, 7/8), (7/8, 1)]

theorem fixedCell02_windows_checked : ClosedWindowCoverCheck fixedCell02Windows := by
  norm_num [fixedCell02Windows, ClosedWindowCoverCheck, ClosedWindowChain]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005
