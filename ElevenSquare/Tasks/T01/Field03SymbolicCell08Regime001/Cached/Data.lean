import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime001.Data
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
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk15
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime001.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk13.entry_202_00,
   Field03SymbolicSignCache.Chunk09.entry_145_00,
   Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk07.entry_124_00,
   Field03SymbolicSignCache.Chunk09.entry_155_00,
   Field03SymbolicSignCache.Chunk12.entry_201_00,
   Field03SymbolicSignCache.Chunk06.entry_107_00,
   Field03SymbolicSignCache.Chunk09.entry_156_00,
   Field03SymbolicSignCache.Chunk07.entry_126_00,
   Field03SymbolicSignCache.Chunk10.entry_165_00,
   Field03SymbolicSignCache.Chunk15.entry_234_00,
   Field03SymbolicSignCache.Chunk06.entry_096_00,
   Field03SymbolicSignCache.Chunk11.entry_177_00,
   Field03SymbolicSignCache.Chunk13.entry_206_00,
   Field03SymbolicSignCache.Chunk05.entry_086_00,
   Field03SymbolicSignCache.Chunk06.entry_105_00,
   Field03SymbolicSignCache.Chunk14.entry_229_00,
   Field03SymbolicSignCache.Chunk14.entry_224_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk11.entry_181_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk07.entry_125_00,
   Field03SymbolicSignCache.Chunk07.entry_127_00,
   Field03SymbolicSignCache.Chunk13.entry_217_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk07.entry_121_00,
   Field03SymbolicSignCache.Chunk08.entry_135_00,
   Field03SymbolicSignCache.Chunk07.entry_117_00,
   Field03SymbolicSignCache.Chunk11.entry_182_00,
   Field03SymbolicSignCache.Chunk09.entry_147_00,
   Field03SymbolicSignCache.Chunk12.entry_194_00,
   Field03SymbolicSignCache.Chunk12.entry_193_00,
   Field03SymbolicSignCache.Chunk14.entry_227_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk14.entry_225_00,
   Field03SymbolicSignCache.Chunk06.entry_103_00,
   Field03SymbolicSignCache.Chunk10.entry_162_00,
   Field03SymbolicSignCache.Chunk14.entry_219_00,
   Field03SymbolicSignCache.Chunk09.entry_150_00,
   Field03SymbolicSignCache.Chunk08.entry_141_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_202_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_145_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_124_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_155_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_201_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_107_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_156_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_126_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_165_00.Check ∧ Field03SymbolicSignCache.Chunk15.entry_234_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_096_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_177_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_206_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_086_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_105_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_229_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_224_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_181_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_125_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_127_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_217_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_121_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_135_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_117_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_182_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_147_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_194_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_193_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_227_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk14.entry_225_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_103_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_162_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_219_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_150_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_141_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk13.entry_202_00_checked, Field03SymbolicSignCache.Chunk09.entry_145_00_checked, Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk07.entry_124_00_checked, Field03SymbolicSignCache.Chunk09.entry_155_00_checked, Field03SymbolicSignCache.Chunk12.entry_201_00_checked, Field03SymbolicSignCache.Chunk06.entry_107_00_checked, Field03SymbolicSignCache.Chunk09.entry_156_00_checked, Field03SymbolicSignCache.Chunk07.entry_126_00_checked, Field03SymbolicSignCache.Chunk10.entry_165_00_checked, Field03SymbolicSignCache.Chunk15.entry_234_00_checked, Field03SymbolicSignCache.Chunk06.entry_096_00_checked, Field03SymbolicSignCache.Chunk11.entry_177_00_checked, Field03SymbolicSignCache.Chunk13.entry_206_00_checked, Field03SymbolicSignCache.Chunk05.entry_086_00_checked, Field03SymbolicSignCache.Chunk06.entry_105_00_checked, Field03SymbolicSignCache.Chunk14.entry_229_00_checked, Field03SymbolicSignCache.Chunk14.entry_224_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk11.entry_181_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk07.entry_125_00_checked, Field03SymbolicSignCache.Chunk07.entry_127_00_checked, Field03SymbolicSignCache.Chunk13.entry_217_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk07.entry_121_00_checked, Field03SymbolicSignCache.Chunk08.entry_135_00_checked, Field03SymbolicSignCache.Chunk07.entry_117_00_checked, Field03SymbolicSignCache.Chunk11.entry_182_00_checked, Field03SymbolicSignCache.Chunk09.entry_147_00_checked, Field03SymbolicSignCache.Chunk12.entry_194_00_checked, Field03SymbolicSignCache.Chunk12.entry_193_00_checked, Field03SymbolicSignCache.Chunk14.entry_227_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk14.entry_225_00_checked, Field03SymbolicSignCache.Chunk06.entry_103_00_checked, Field03SymbolicSignCache.Chunk10.entry_162_00_checked, Field03SymbolicSignCache.Chunk14.entry_219_00_checked, Field03SymbolicSignCache.Chunk09.entry_150_00_checked, Field03SymbolicSignCache.Chunk08.entry_141_00_checked, trivial⟩

def signNode002 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨3, (1/1000000)⟩, ⟨4, (1/500000)⟩, ⟨5, 1⟩, ⟨6, (1/400000000000000000000000000000000)⟩⟩,
    ⟨⟨7, (1/500000)⟩, ⟨8, (1/1000000)⟩, ⟨5, 1⟩, ⟨9, (1/400000000000000000000000000000000)⟩⟩]

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨10, (1/500000)⟩, ⟨11, (1/1000000)⟩, ⟨5, 1⟩, ⟨12, (1/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨13, (1/3820000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨14, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨15, (1/500000)⟩, ⟨16, (1/1000000)⟩, ⟨5, 1⟩, ⟨17, (1/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨18, (1/1000000)⟩, ⟨5, (180838398927797548822990812349238221/3820000000000000000000000000000000000)⟩, ⟨19, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨20, (387708359002281417731/1528000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨10, (1/500000)⟩, ⟨5, (204491442791316111067898321413378327/3820000000000000000000000000000000000)⟩, ⟨21, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨22, (387708359002281417731/1528000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨10, (1/500000)⟩, ⟨5, (65205323920018353738655255774264603/3820000000000000000000000000000000000)⟩, ⟨23, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨24, (387708359002281417731/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨18, (1/1000000)⟩, ⟨5, (216709074577309368174821609880685753/3820000000000000000000000000000000000)⟩, ⟨25, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨26, (387708359002281417731/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨10, (1/500000)⟩, ⟨5, (26969676671133446480655357718764293/382000000000000000000000000000000000)⟩, ⟨27, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨28, (11243542411066161114199/764000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨18, (1/1000000)⟩, ⟨5, (198773736752553458498906211114961987/1910000000000000000000000000000000000)⟩, ⟨29, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨30, (11243542411066161114199/764000000000000000000000000000000000000000000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode003

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨31, (1/3820000000000000000000000000000)⟩⟩,
    ⟨⟨5, (1063111/1000000)⟩, ⟨18, (1/1000000)⟩, ⟨2, 2⟩, ⟨32, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨0, 1⟩, ⟨5, 1⟩, ⟨33, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨18, (1/1000000)⟩, ⟨34, (1/500000)⟩, ⟨5, 1⟩, ⟨35, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨36, (1063111/1000000)⟩, ⟨36, (180838398927797548822990812349238221/3820000000000000000000000000000000000)⟩, ⟨36, (345577383861464050670137527423/3820000000000000000000000000000)⟩, ⟨37, (387708359002281417731/1528000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨5, (345577383861464050670137527423/3820000000000000000000000000000)⟩, ⟨19, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨38, (387708359002281417731/19100000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨5, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨25, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨39, (387708359002281417731/28500781250000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨36, (1063111/1000000)⟩, ⟨36, (216709074577309368174821609880685753/3820000000000000000000000000000000000)⟩, ⟨36, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨40, (387708359002281417731/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨5, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨29, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨41, (11243542411066161114199/9550000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨36, (1063111/1000000)⟩, ⟨36, (198773736752553458498906211114961987/1910000000000000000000000000000000000)⟩, ⟨36, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨42, (78704796877463127799393/764000000000000000000000000000000000000000000000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode004

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime001.Cached
