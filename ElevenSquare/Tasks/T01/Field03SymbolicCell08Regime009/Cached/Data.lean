import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Data
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
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk12
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk13
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk14
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk07.entry_113_00,
   Field03SymbolicSignCache.Chunk10.entry_161_00,
   Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk03.entry_060_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk04.entry_072_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk13.entry_204_00,
   Field03SymbolicSignCache.Chunk02.entry_046_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk05.entry_091_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk03.entry_062_00,
   Field03SymbolicSignCache.Chunk04.entry_070_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk00.entry_010_00,
   Field03SymbolicSignCache.Chunk14.entry_229_00,
   Field03SymbolicSignCache.Chunk08.entry_142_00,
   Field03SymbolicSignCache.Chunk01.entry_018_00,
   Field03SymbolicSignCache.Chunk03.entry_056_00,
   Field03SymbolicSignCache.Chunk06.entry_100_00,
   Field03SymbolicSignCache.Chunk10.entry_164_00,
   Field03SymbolicSignCache.Chunk05.entry_095_00,
   Field03SymbolicSignCache.Chunk00.entry_001_00,
   Field03SymbolicSignCache.Chunk04.entry_077_00,
   Field03SymbolicSignCache.Chunk13.entry_211_00,
   Field03SymbolicSignCache.Chunk07.entry_126_00,
   Field03SymbolicSignCache.Chunk09.entry_156_00,
   Field03SymbolicSignCache.Chunk14.entry_223_00,
   Field03SymbolicSignCache.Chunk01.entry_030_00,
   Field03SymbolicSignCache.Chunk14.entry_226_00,
   Field03SymbolicSignCache.Chunk09.entry_155_00,
   Field03SymbolicSignCache.Chunk12.entry_201_00,
   Field03SymbolicSignCache.Chunk07.entry_120_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk07.entry_113_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_161_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_060_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_072_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_204_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_046_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk05.entry_091_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_062_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_070_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_010_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_229_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_142_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_018_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_056_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_100_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_164_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_095_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_001_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_077_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_211_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_126_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_156_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_223_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_030_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_226_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_155_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_201_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_120_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk07.entry_113_00_checked, Field03SymbolicSignCache.Chunk10.entry_161_00_checked, Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk03.entry_060_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk04.entry_072_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk13.entry_204_00_checked, Field03SymbolicSignCache.Chunk02.entry_046_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk05.entry_091_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk03.entry_062_00_checked, Field03SymbolicSignCache.Chunk04.entry_070_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk00.entry_010_00_checked, Field03SymbolicSignCache.Chunk14.entry_229_00_checked, Field03SymbolicSignCache.Chunk08.entry_142_00_checked, Field03SymbolicSignCache.Chunk01.entry_018_00_checked, Field03SymbolicSignCache.Chunk03.entry_056_00_checked, Field03SymbolicSignCache.Chunk06.entry_100_00_checked, Field03SymbolicSignCache.Chunk10.entry_164_00_checked, Field03SymbolicSignCache.Chunk05.entry_095_00_checked, Field03SymbolicSignCache.Chunk00.entry_001_00_checked, Field03SymbolicSignCache.Chunk04.entry_077_00_checked, Field03SymbolicSignCache.Chunk13.entry_211_00_checked, Field03SymbolicSignCache.Chunk07.entry_126_00_checked, Field03SymbolicSignCache.Chunk09.entry_156_00_checked, Field03SymbolicSignCache.Chunk14.entry_223_00_checked, Field03SymbolicSignCache.Chunk01.entry_030_00_checked, Field03SymbolicSignCache.Chunk14.entry_226_00_checked, Field03SymbolicSignCache.Chunk09.entry_155_00_checked, Field03SymbolicSignCache.Chunk12.entry_201_00_checked, Field03SymbolicSignCache.Chunk07.entry_120_00_checked, trivial⟩

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨3, (1/500000)⟩, ⟨4, 1⟩, ⟨5, (1/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨6, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨4, (60518064412892839742239758396474331/764000000000000000000000000000000000)⟩, ⟨7, (1/1000000)⟩, ⟨8, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨9, (387708359002281417731/2918480000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨4, (87096559311764346689203612327141981/3820000000000000000000000000000000000)⟩, ⟨8, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨10, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨11, (172788692124586204836209472577/3820000000000000000000000000000)⟩, ⟨11, (172788692124586204836209472577/3820000000000000000000000000000)⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨11, (204491442791316111067898321413378327/3820000000000000000000000000000000000)⟩, ⟨11, (65205323920018353738655255774264603/3820000000000000000000000000000000000)⟩, ⟨11, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨12, (150317771640241930449364231724863321188361/435491937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨4, (107165571094414180829766959335633801/3820000000000000000000000000000000000)⟩, ⟨13, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨14, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨11, (204491442791316111067898321413378327/3820000000000000000000000000000000000)⟩, ⟨11, (26969676671133446480655357718764293/382000000000000000000000000000000000)⟩, ⟨11, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨15, (4359215377567015983031562720021036314462469/45601250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (1/1000000)⟩, ⟨4, (97131065203089263759485285831387891/1910000000000000000000000000000000000)⟩, ⟨16, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨17, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩]

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨8, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨4, 1⟩, ⟨18, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨19, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨18, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨4, 1⟩, ⟨8, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨20, (387708359002281417731/382000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨21, (1/200000000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨6, 2⟩, ⟨1, 1⟩, ⟨22, (1/1910000000000000000000000000000)⟩⟩]

def signNode002 : SymbolicCoverSignRefs :=
  .split signNode003 signNode004

def signNode005 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨6, 2⟩, ⟨4, 1⟩, ⟨23, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨6, 2⟩, ⟨1, 1⟩, ⟨24, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨25, (1/5000000000000000000000)⟩⟩,
    ⟨⟨6, 2⟩, ⟨0, 1⟩, ⟨4, 1⟩, ⟨26, (1/5000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode005

def signNode006 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨27, (1/5000000000000000000000)⟩⟩,
    ⟨⟨28, (1/1000000)⟩, ⟨29, (1/500000)⟩, ⟨4, 1⟩, ⟨30, (1/400000000000000000000000000000000)⟩⟩,
    ⟨⟨4, (19677/50000)⟩, ⟨31, (1/500000)⟩, ⟨6, 2⟩, ⟨32, (1/200000000000000000000000000000000)⟩⟩,
    ⟨⟨33, (1/500000)⟩, ⟨34, (1/1000000)⟩, ⟨4, 1⟩, ⟨35, (1/400000000000000000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode006

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached
