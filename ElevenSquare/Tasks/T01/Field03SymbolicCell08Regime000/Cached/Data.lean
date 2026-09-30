import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCachedCover
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk05
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk06
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk07
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk08
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk09
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk10
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk11
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk12
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk13
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk14
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk09.entry_156_00,
   Field03SymbolicSignCache.Chunk07.entry_126_00,
   Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk13.entry_203_00,
   Field03SymbolicSignCache.Chunk06.entry_105_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk09.entry_147_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk12.entry_193_00,
   Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Chunk14.entry_220_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk14.entry_225_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk09.entry_154_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk10.entry_163_00,
   Field03SymbolicSignCache.Chunk14.entry_219_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk09.entry_149_00,
   Field03SymbolicSignCache.Chunk08.entry_141_00,
   Field03SymbolicSignCache.Chunk12.entry_194_00,
   Field03SymbolicSignCache.Chunk06.entry_096_00,
   Field03SymbolicSignCache.Chunk13.entry_202_00,
   Field03SymbolicSignCache.Chunk09.entry_145_00,
   Field03SymbolicSignCache.Chunk07.entry_112_00,
   Field03SymbolicSignCache.Chunk11.entry_187_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk09.entry_156_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_126_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_203_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_105_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_147_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk12.entry_193_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_220_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk14.entry_225_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_154_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_163_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_219_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_149_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_141_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_194_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_096_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_202_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_145_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_112_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_187_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk09.entry_156_00_checked, Field03SymbolicSignCache.Chunk07.entry_126_00_checked, Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk13.entry_203_00_checked, Field03SymbolicSignCache.Chunk06.entry_105_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk09.entry_147_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk12.entry_193_00_checked, Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Chunk14.entry_220_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk14.entry_225_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk09.entry_154_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk10.entry_163_00_checked, Field03SymbolicSignCache.Chunk14.entry_219_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk09.entry_149_00_checked, Field03SymbolicSignCache.Chunk08.entry_141_00_checked, Field03SymbolicSignCache.Chunk12.entry_194_00_checked, Field03SymbolicSignCache.Chunk06.entry_096_00_checked, Field03SymbolicSignCache.Chunk13.entry_202_00_checked, Field03SymbolicSignCache.Chunk09.entry_145_00_checked, Field03SymbolicSignCache.Chunk07.entry_112_00_checked, Field03SymbolicSignCache.Chunk11.entry_187_00_checked, trivial⟩

def signNode001 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, (1/500000)⟩, ⟨1, (1/1000000)⟩, ⟨2, 1⟩, ⟨3, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1063111/1000000)⟩, ⟨4, (1/1000000)⟩, ⟨5, 2⟩, ⟨6, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨5, 2⟩, ⟨5, 2⟩, ⟨7, 1⟩, ⟨7, 1⟩⟩,
    ⟨⟨2, (1063111/1000000)⟩, ⟨8, (1/500000)⟩, ⟨9, 1⟩, ⟨10, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨11, (1063111/1000000)⟩, ⟨11, (180838398927797548822990812349238221/3820000000000000000000000000000000000)⟩, ⟨11, (345577383861464050670137527423/3820000000000000000000000000000)⟩, ⟨12, (387708359002281417731/1528000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (1/500000)⟩, ⟨2, (204491442791316111067898321413378327/3820000000000000000000000000000000000)⟩, ⟨13, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨14, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (1/500000)⟩, ⟨2, (65205323920018353738655255774264603/3820000000000000000000000000000000000)⟩, ⟨15, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨16, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨11, (1063111/1000000)⟩, ⟨11, (216709074577309368174821609880685753/3820000000000000000000000000000000000)⟩, ⟨11, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨17, (387708359002281417731/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (1/500000)⟩, ⟨2, (26969676671133446480655357718764293/382000000000000000000000000000000000)⟩, ⟨18, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨19, (11243542411066161114199/1459240000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨11, (1063111/1000000)⟩, ⟨11, (198773736752553458498906211114961987/1910000000000000000000000000000000000)⟩, ⟨11, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨20, (78704796877463127799393/764000000000000000000000000000000000000000000000000000000000000)⟩⟩]

def signNode002 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨9, 1⟩, ⟨5, 2⟩, ⟨2, 1⟩, ⟨21, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨5, 2⟩, ⟨5, 2⟩, ⟨7, 1⟩, ⟨22, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨23, (1/1000000)⟩, ⟨24, (1/500000)⟩, ⟨2, 1⟩, ⟨25, (1/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 1⟩, ⟨5, 2⟩, ⟨9, 1⟩, ⟨26, (1/100000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode002

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.Cached
