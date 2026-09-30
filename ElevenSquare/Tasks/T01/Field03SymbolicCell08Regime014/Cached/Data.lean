import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCachedCover
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk00
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk01
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk02
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk03
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk04
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk05
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk06
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk07
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk08
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk11
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk12
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk13
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk14
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk15
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk12.entry_193_00,
   Field03SymbolicSignCache.Chunk06.entry_105_00,
   Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk02.entry_045_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk07.entry_126_00,
   Field03SymbolicSignCache.Chunk02.entry_036_00,
   Field03SymbolicSignCache.Chunk06.entry_109_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk00.entry_012_00,
   Field03SymbolicSignCache.Chunk05.entry_090_00,
   Field03SymbolicSignCache.Chunk00.entry_000_00,
   Field03SymbolicSignCache.Chunk01.entry_019_00,
   Field03SymbolicSignCache.Chunk01.entry_027_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk01.entry_022_00,
   Field03SymbolicSignCache.Chunk01.entry_026_00,
   Field03SymbolicSignCache.Chunk03.entry_058_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk04.entry_076_00,
   Field03SymbolicSignCache.Chunk12.entry_194_01,
   Field03SymbolicSignCache.Chunk06.entry_096_00,
   Field03SymbolicSignCache.Chunk15.entry_234_00,
   Field03SymbolicSignCache.Chunk03.entry_054_00,
   Field03SymbolicSignCache.Chunk11.entry_182_00,
   Field03SymbolicSignCache.Chunk01.entry_030_00,
   Field03SymbolicSignCache.Chunk13.entry_202_00,
   Field03SymbolicSignCache.Chunk07.entry_122_00,
   Field03SymbolicSignCache.Chunk02.entry_034_00,
   Field03SymbolicSignCache.Chunk14.entry_232_00,
   Field03SymbolicSignCache.Chunk11.entry_187_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk12.entry_193_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_105_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_045_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_126_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_036_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_109_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_012_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_090_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_000_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_019_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_027_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_022_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_026_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_058_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_076_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_194_01.Check ∧ Field03SymbolicSignCache.Chunk06.entry_096_00.Check ∧ Field03SymbolicSignCache.Chunk15.entry_234_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_054_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_182_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_030_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_202_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_122_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_034_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_232_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_187_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk12.entry_193_00_checked, Field03SymbolicSignCache.Chunk06.entry_105_00_checked, Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk02.entry_045_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk07.entry_126_00_checked, Field03SymbolicSignCache.Chunk02.entry_036_00_checked, Field03SymbolicSignCache.Chunk06.entry_109_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk00.entry_012_00_checked, Field03SymbolicSignCache.Chunk05.entry_090_00_checked, Field03SymbolicSignCache.Chunk00.entry_000_00_checked, Field03SymbolicSignCache.Chunk01.entry_019_00_checked, Field03SymbolicSignCache.Chunk01.entry_027_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk01.entry_022_00_checked, Field03SymbolicSignCache.Chunk01.entry_026_00_checked, Field03SymbolicSignCache.Chunk03.entry_058_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk04.entry_076_00_checked, Field03SymbolicSignCache.Chunk12.entry_194_01_checked, Field03SymbolicSignCache.Chunk06.entry_096_00_checked, Field03SymbolicSignCache.Chunk15.entry_234_00_checked, Field03SymbolicSignCache.Chunk03.entry_054_00_checked, Field03SymbolicSignCache.Chunk11.entry_182_00_checked, Field03SymbolicSignCache.Chunk01.entry_030_00_checked, Field03SymbolicSignCache.Chunk13.entry_202_00_checked, Field03SymbolicSignCache.Chunk07.entry_122_00_checked, Field03SymbolicSignCache.Chunk02.entry_034_00_checked, Field03SymbolicSignCache.Chunk14.entry_232_00_checked, Field03SymbolicSignCache.Chunk11.entry_187_00_checked, trivial⟩

def signNode002 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨2, (1/500000)⟩, ⟨3, (1/1000000)⟩, ⟨4, 1⟩, ⟨5, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨6, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨7, (1/1000000)⟩, ⟨8, (1/500000)⟩, ⟨4, 1⟩, ⟨9, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/500000)⟩, ⟨4, (180838398927797548822990812349238221/3820000000000000000000000000000000000)⟩, ⟨10, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨11, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨7, (1/1000000)⟩, ⟨4, (204491442791316111067898321413378327/3820000000000000000000000000000000000)⟩, ⟨12, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨13, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨7, (1/1000000)⟩, ⟨4, (65205323920018353738655255774264603/3820000000000000000000000000000000000)⟩, ⟨14, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨15, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/500000)⟩, ⟨4, (216709074577309368174821609880685753/3820000000000000000000000000000000000)⟩, ⟨16, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨17, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨7, (1/1000000)⟩, ⟨4, (26969676671133446480655357718764293/382000000000000000000000000000000000)⟩, ⟨18, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨19, (11243542411066161114199/1459240000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/500000)⟩, ⟨4, (198773736752553458498906211114961987/1910000000000000000000000000000000000)⟩, ⟨20, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨21, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩]

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨6, 2⟩, ⟨4, 1⟩, ⟨22, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨6, 2⟩, ⟨1, 1⟩, ⟨23, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨24, (1/3820000000000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨0, 1⟩, ⟨4, 1⟩, ⟨25, (1/3820000000000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode003

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨26, (1/3820000000000000000000000000000)⟩⟩,
    ⟨⟨27, (1/500000)⟩, ⟨28, (1/1000000)⟩, ⟨4, 1⟩, ⟨29, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, (116361/250000)⟩, ⟨30, (1/500000)⟩, ⟨6, 2⟩, ⟨31, (1/200000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨6, 2⟩, ⟨0, 1⟩, ⟨32, (1/100000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode004

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached
