import ElevenSquare.Pending.S07_GridPairChecks0
import ElevenSquare.Pending.S07_GridPairChecks1
import ElevenSquare.Pending.S07_GridPairChecks2
import ElevenSquare.Pending.S07_GridPairChecks3
import ElevenSquare.Pending.S07_GridPairChecks4
import ElevenSquare.Pending.S07_GridPairChecks5
import ElevenSquare.Pending.S07_GridPairChecks6
import ElevenSquare.Pending.S07_GridPairChecks7
import ElevenSquare.Pending.S07_GridPairChecks8
import ElevenSquare.Pending.S07_GridPairChecks9
import ElevenSquare.Pending.S07_GridPairChecks10
import ElevenSquare.Pending.S07_GridPairChecks11
import ElevenSquare.Pending.S07_GridPairChecks12
import ElevenSquare.Pending.S07_GridPairChecks13
import ElevenSquare.Pending.S07_GridPairChecks14
import ElevenSquare.Pending.S07_GridPairChecks15
import ElevenSquare.Pending.S07_GridPairChecks16
import ElevenSquare.Pending.S07_GridPairChecks17
import ElevenSquare.Pending.S07_GridPairChecks18
import ElevenSquare.Pending.S07_GridPairChecks19
import ElevenSquare.Pending.S07_GridPairChecks20
import ElevenSquare.Pending.S07_GridPairChecks21
import ElevenSquare.Pending.S07_GridPairChecks22
import ElevenSquare.Pending.S07_GridPairChecks23
import ElevenSquare.Pending.S07_GridPairChecks24
namespace ElevenSquare.Pending.GridDistance
theorem all_bans_checked : ∀ pr ∈ bannedPairArray.toList, indexedCheck pr = true := by
  unfold bannedPairArray
  exact (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append (checks_append bans_checked_chunk0 bans_checked_chunk1) bans_checked_chunk2) bans_checked_chunk3) bans_checked_chunk4) bans_checked_chunk5) bans_checked_chunk6) bans_checked_chunk7) bans_checked_chunk8) bans_checked_chunk9) bans_checked_chunk10) bans_checked_chunk11) bans_checked_chunk12) bans_checked_chunk13) bans_checked_chunk14) bans_checked_chunk15) bans_checked_chunk16) bans_checked_chunk17) bans_checked_chunk18) bans_checked_chunk19) bans_checked_chunk20) bans_checked_chunk21) bans_checked_chunk22) bans_checked_chunk23) bans_checked_chunk24)
end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.all_bans_checked
