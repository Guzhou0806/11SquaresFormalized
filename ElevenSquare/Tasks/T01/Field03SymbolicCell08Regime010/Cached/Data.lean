import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Data
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
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk09
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk10
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk11
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk12
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk13
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk14
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk07.entry_113_00,
   Field03SymbolicSignCache.Chunk10.entry_161_00,
   Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk05.entry_088_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk11.entry_177_00,
   Field03SymbolicSignCache.Chunk04.entry_072_00,
   Field03SymbolicSignCache.Chunk11.entry_180_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk03.entry_051_00,
   Field03SymbolicSignCache.Chunk05.entry_090_00,
   Field03SymbolicSignCache.Chunk02.entry_047_00,
   Field03SymbolicSignCache.Chunk01.entry_019_00,
   Field03SymbolicSignCache.Chunk05.entry_080_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk03.entry_062_00,
   Field03SymbolicSignCache.Chunk01.entry_026_00,
   Field03SymbolicSignCache.Chunk02.entry_044_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk00.entry_010_00,
   Field03SymbolicSignCache.Chunk10.entry_164_01,
   Field03SymbolicSignCache.Chunk05.entry_095_00,
   Field03SymbolicSignCache.Chunk04.entry_074_00,
   Field03SymbolicSignCache.Chunk03.entry_053_00,
   Field03SymbolicSignCache.Chunk11.entry_182_00,
   Field03SymbolicSignCache.Chunk07.entry_126_00,
   Field03SymbolicSignCache.Chunk09.entry_156_00,
   Field03SymbolicSignCache.Chunk10.entry_165_01,
   Field03SymbolicSignCache.Chunk01.entry_030_00,
   Field03SymbolicSignCache.Chunk14.entry_226_00,
   Field03SymbolicSignCache.Chunk11.entry_187_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk07.entry_113_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_161_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_088_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_177_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_072_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_180_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_051_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_090_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_047_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_019_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_080_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_062_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_026_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_044_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_010_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_164_01.Check ∧ Field03SymbolicSignCache.Chunk05.entry_095_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_074_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_053_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_182_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_126_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_156_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_165_01.Check ∧ Field03SymbolicSignCache.Chunk01.entry_030_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_226_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_187_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk07.entry_113_00_checked, Field03SymbolicSignCache.Chunk10.entry_161_00_checked, Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk05.entry_088_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk11.entry_177_00_checked, Field03SymbolicSignCache.Chunk04.entry_072_00_checked, Field03SymbolicSignCache.Chunk11.entry_180_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk03.entry_051_00_checked, Field03SymbolicSignCache.Chunk05.entry_090_00_checked, Field03SymbolicSignCache.Chunk02.entry_047_00_checked, Field03SymbolicSignCache.Chunk01.entry_019_00_checked, Field03SymbolicSignCache.Chunk05.entry_080_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk03.entry_062_00_checked, Field03SymbolicSignCache.Chunk01.entry_026_00_checked, Field03SymbolicSignCache.Chunk02.entry_044_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk00.entry_010_00_checked, Field03SymbolicSignCache.Chunk10.entry_164_01_checked, Field03SymbolicSignCache.Chunk05.entry_095_00_checked, Field03SymbolicSignCache.Chunk04.entry_074_00_checked, Field03SymbolicSignCache.Chunk03.entry_053_00_checked, Field03SymbolicSignCache.Chunk11.entry_182_00_checked, Field03SymbolicSignCache.Chunk07.entry_126_00_checked, Field03SymbolicSignCache.Chunk09.entry_156_00_checked, Field03SymbolicSignCache.Chunk10.entry_165_01_checked, Field03SymbolicSignCache.Chunk01.entry_030_00_checked, Field03SymbolicSignCache.Chunk14.entry_226_00_checked, Field03SymbolicSignCache.Chunk11.entry_187_00_checked, trivial⟩

def signNode002 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨3, (1/500000)⟩, ⟨4, 1⟩, ⟨5, (1/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨6, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨7, (1/500000)⟩, ⟨8, (1/1000000)⟩, ⟨4, 1⟩, ⟨9, (1/764000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨4, (87096559311764346689203612327141981/3820000000000000000000000000000000000)⟩, ⟨10, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨11, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨7, (1/500000)⟩, ⟨4, (60518064412892839742239758396474331/764000000000000000000000000000000000)⟩, ⟨12, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨13, (387708359002281417731/2918480000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨7, (1/500000)⟩, ⟨4, (176783789618754520241628486413902859/3820000000000000000000000000000000000)⟩, ⟨14, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨15, (387708359002281417731/2918480000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨4, (107165571094414180829766959335633801/3820000000000000000000000000000000000)⟩, ⟨16, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨17, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨7, (1/500000)⟩, ⟨4, (239687055841609359476413639198137257/1910000000000000000000000000000000000)⟩, ⟨18, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨19, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨4, (97131065203089263759485285831387891/1910000000000000000000000000000000000)⟩, ⟨20, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨21, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩]

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
    ⟨⟨27, (1/1000000)⟩, ⟨28, (1/500000)⟩, ⟨4, 1⟩, ⟨29, (1/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, (19677/50000)⟩, ⟨30, (1/500000)⟩, ⟨6, 2⟩, ⟨31, (1/200000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨6, 2⟩, ⟨0, 1⟩, ⟨32, (1/100000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode004

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached
