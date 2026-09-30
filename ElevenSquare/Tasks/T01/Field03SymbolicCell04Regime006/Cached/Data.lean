import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Data
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
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk11
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk12
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk13
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk14
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Constants

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk00.entry_004_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk08.entry_129_00,
   Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk07.entry_113_00,
   Field03SymbolicSignCache.Chunk12.entry_192_00,
   Field03SymbolicSignCache.Chunk14.entry_229_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk11.entry_186_00,
   Field03SymbolicSignCache.Chunk04.entry_067_00,
   Field03SymbolicSignCache.Chunk08.entry_133_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk00.entry_013_00,
   Field03SymbolicSignCache.Chunk05.entry_081_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk02.entry_038_00,
   Field03SymbolicSignCache.Chunk01.entry_026_00,
   Field03SymbolicSignCache.Chunk11.entry_184_00,
   Field03SymbolicSignCache.Chunk12.entry_199_00,
   Field03SymbolicSignCache.Chunk09.entry_158_00,
   Field03SymbolicSignCache.Chunk13.entry_209_00,
   Field03SymbolicSignCache.Chunk05.entry_082_00,
   Field03SymbolicSignCache.Chunk06.entry_111_00,
   Field03SymbolicSignCache.Chunk09.entry_143_00,
   Field03SymbolicSignCache.Chunk14.entry_222_00,
   Field03SymbolicSignCache.Chunk05.entry_094_00,
   Field03SymbolicSignCache.Chunk06.entry_110_00,
   Field03SymbolicSignCache.Chunk08.entry_134_00,
   Field03SymbolicSignCache.Chunk00.entry_005_00,
   Field03SymbolicSignCache.Chunk11.entry_173_00,
   Field03SymbolicSignCache.Chunk11.entry_174_00,
   Field03SymbolicSignCache.Chunk03.entry_061_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_004_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_129_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk07.entry_113_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_192_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_229_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_186_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_067_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_133_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_013_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_081_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk02.entry_038_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_026_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_184_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_199_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_158_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_209_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_082_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_111_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_143_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_222_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_094_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_110_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_134_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_005_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_173_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_174_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_061_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk00.entry_004_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk08.entry_129_00_checked, Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk07.entry_113_00_checked, Field03SymbolicSignCache.Chunk12.entry_192_00_checked, Field03SymbolicSignCache.Chunk14.entry_229_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk11.entry_186_00_checked, Field03SymbolicSignCache.Chunk04.entry_067_00_checked, Field03SymbolicSignCache.Chunk08.entry_133_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk00.entry_013_00_checked, Field03SymbolicSignCache.Chunk05.entry_081_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk02.entry_038_00_checked, Field03SymbolicSignCache.Chunk01.entry_026_00_checked, Field03SymbolicSignCache.Chunk11.entry_184_00_checked, Field03SymbolicSignCache.Chunk12.entry_199_00_checked, Field03SymbolicSignCache.Chunk09.entry_158_00_checked, Field03SymbolicSignCache.Chunk13.entry_209_00_checked, Field03SymbolicSignCache.Chunk05.entry_082_00_checked, Field03SymbolicSignCache.Chunk06.entry_111_00_checked, Field03SymbolicSignCache.Chunk09.entry_143_00_checked, Field03SymbolicSignCache.Chunk14.entry_222_00_checked, Field03SymbolicSignCache.Chunk05.entry_094_00_checked, Field03SymbolicSignCache.Chunk06.entry_110_00_checked, Field03SymbolicSignCache.Chunk08.entry_134_00_checked, Field03SymbolicSignCache.Chunk00.entry_005_00_checked, Field03SymbolicSignCache.Chunk11.entry_173_00_checked, Field03SymbolicSignCache.Chunk11.entry_174_00_checked, Field03SymbolicSignCache.Chunk03.entry_061_00_checked, trivial⟩

def signNode002 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, (367197/1000000)⟩, ⟨1, (3/1000000)⟩, ⟨2, 2⟩, ⟨3, (3/12500000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, (52819/100000)⟩, ⟨6, (1/1000000)⟩, ⟨4, 1⟩, ⟨7, (1/191000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨2, 2⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, 1⟩, ⟨8, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨9, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨10, (150317771640241930449364231724863321188361/14592400000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨6, (1/1000000)⟩, ⟨0, (87096559311764346689203612327141981/3820000000000000000000000000000000000)⟩, ⟨9, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨11, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (3/1000000)⟩, ⟨0, (20980123587197913545555851780684599/1910000000000000000000000000000000000)⟩, ⟨13, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨14, (1163125077006844253193/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨0, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨13, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨15, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨16, (367197/1000000)⟩, ⟨16, (18858659076288984321895751381216787/955000000000000000000000000000000000)⟩, ⟨16, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨17, (33730627233198483342597/47750000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨0, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨18, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨19, (11243542411066161114199/4775000000000000000000000000000000000000000000000000)⟩⟩]

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨20, (1/5000000000000000000000)⟩⟩,
    ⟨⟨21, (1/500000)⟩, ⟨22, (1/500000)⟩, ⟨0, 1⟩, ⟨23, (1/100000000000000000000000000000000)⟩⟩,
    ⟨⟨24, (23/500000)⟩, ⟨25, (23/250000)⟩, ⟨0, 1⟩, ⟨26, (23/955000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨2, 2⟩, ⟨5, 1⟩, ⟨27, (1/1910000000000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode003

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨4, 1⟩, ⟨2, 2⟩, ⟨28, (1/500000000)⟩⟩,
    ⟨⟨29, (3/1000000)⟩, ⟨30, (3/1000000)⟩, ⟨0, 1⟩, ⟨31, (3/25000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨32, (1/5000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨4, 1⟩, ⟨0, 1⟩, ⟨33, (1/5000000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode004

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached
