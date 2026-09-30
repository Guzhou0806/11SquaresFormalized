import ElevenSquare.Tasks.T01.ClosedWindowCover

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005
noncomputable section

def hybridCell01Windows : List (ℚ × ℚ) := [
  (0, 1/512), (1/512, 1/256), (1/256, 1/64), (1/64, 5/256), (5/256, 7/128), (7/128, 1/16), (1/16, 5/64), (5/64, 3/32), (3/32, 7/64), (7/64, 1/8), (1/8, 5/32), (5/32, 11/64), (11/64, 3/16), (3/16, 7/32), (7/32, 1/4), (1/4, 9/32), (9/32, 19/64), (19/64, 5/16), (5/16, 41/128), (41/128, 21/64), (21/64, 91/256), (91/256, 25/64), (25/64, 101/256), (101/256, 61/128), (61/128, 31/64), (31/64, 1/2), (1/2, 19/32), (19/32, 5/8), (5/8, 21/32), (21/32, 11/16), (11/16, 23/32), (23/32, 3/4), (3/4, 27/32), (27/32, 7/8), (7/8, 57/64), (57/64, 115/128), (115/128, 29/32), (29/32, 117/128), (117/128, 59/64), (59/64, 499/512), (499/512, 125/128), (125/128, 1)]

theorem hybridCell01_windows_checked : ClosedWindowCoverCheck hybridCell01Windows := by
  norm_num [hybridCell01Windows, ClosedWindowCoverCheck, ClosedWindowChain]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005
