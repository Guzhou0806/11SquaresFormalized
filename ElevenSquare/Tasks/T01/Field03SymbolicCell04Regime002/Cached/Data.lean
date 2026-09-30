import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Data
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

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk08.entry_133_00,
   Field03SymbolicSignCache.Chunk07.entry_114_00,
   Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk01.entry_021_00,
   Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk07.entry_113_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk07.entry_116_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk12.entry_197_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk04.entry_069_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk00.entry_013_00,
   Field03SymbolicSignCache.Chunk01.entry_019_00,
   Field03SymbolicSignCache.Chunk05.entry_083_00,
   Field03SymbolicSignCache.Chunk07.entry_118_00,
   Field03SymbolicSignCache.Chunk00.entry_008_00,
   Field03SymbolicSignCache.Chunk03.entry_048_00,
   Field03SymbolicSignCache.Chunk06.entry_098_00,
   Field03SymbolicSignCache.Chunk08.entry_135_00,
   Field03SymbolicSignCache.Chunk13.entry_213_00,
   Field03SymbolicSignCache.Chunk02.entry_042_00,
   Field03SymbolicSignCache.Chunk11.entry_178_00,
   Field03SymbolicSignCache.Chunk13.entry_210_00,
   Field03SymbolicSignCache.Chunk14.entry_218_00,
   Field03SymbolicSignCache.Chunk06.entry_111_00,
   Field03SymbolicSignCache.Chunk09.entry_143_00,
   Field03SymbolicSignCache.Chunk14.entry_222_00,
   Field03SymbolicSignCache.Chunk05.entry_094_00,
   Field03SymbolicSignCache.Chunk06.entry_110_00,
   Field03SymbolicSignCache.Chunk09.entry_152_00,
   Field03SymbolicSignCache.Chunk07.entry_123_00,
   Field03SymbolicSignCache.Chunk12.entry_188_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk08.entry_133_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_114_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_021_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk07.entry_113_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_116_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_197_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk04.entry_069_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_013_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_019_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_083_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_118_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_008_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_048_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_098_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_135_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_213_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_042_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_178_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_210_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_218_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_111_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_143_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_222_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_094_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_110_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_152_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_123_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_188_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk08.entry_133_00_checked, Field03SymbolicSignCache.Chunk07.entry_114_00_checked, Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk01.entry_021_00_checked, Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk07.entry_113_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk07.entry_116_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk12.entry_197_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk04.entry_069_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk00.entry_013_00_checked, Field03SymbolicSignCache.Chunk01.entry_019_00_checked, Field03SymbolicSignCache.Chunk05.entry_083_00_checked, Field03SymbolicSignCache.Chunk07.entry_118_00_checked, Field03SymbolicSignCache.Chunk00.entry_008_00_checked, Field03SymbolicSignCache.Chunk03.entry_048_00_checked, Field03SymbolicSignCache.Chunk06.entry_098_00_checked, Field03SymbolicSignCache.Chunk08.entry_135_00_checked, Field03SymbolicSignCache.Chunk13.entry_213_00_checked, Field03SymbolicSignCache.Chunk02.entry_042_00_checked, Field03SymbolicSignCache.Chunk11.entry_178_00_checked, Field03SymbolicSignCache.Chunk13.entry_210_00_checked, Field03SymbolicSignCache.Chunk14.entry_218_00_checked, Field03SymbolicSignCache.Chunk06.entry_111_00_checked, Field03SymbolicSignCache.Chunk09.entry_143_00_checked, Field03SymbolicSignCache.Chunk14.entry_222_00_checked, Field03SymbolicSignCache.Chunk05.entry_094_00_checked, Field03SymbolicSignCache.Chunk06.entry_110_00_checked, Field03SymbolicSignCache.Chunk09.entry_152_00_checked, Field03SymbolicSignCache.Chunk07.entry_123_00_checked, Field03SymbolicSignCache.Chunk12.entry_188_00_checked, trivial⟩

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, (3/1000000)⟩, ⟨1, (3/1000000)⟩, ⟨2, 1⟩, ⟨3, (3/3820000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨2, (97131065203089263759485285831387891/1910000000000000000000000000000000000)⟩, ⟨6, (1/1000000)⟩, ⟨7, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨8, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨9, 2⟩, ⟨9, 2⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨7, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨10, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨2, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨11, (180811528186321114874026805534919308661692598193890041076586695645506475377787/435491937500000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (33089003689562761634586927661147991/955000000000000000000000000000000000)⟩, ⟨12, (11354117646119725680999490740947719/1910000000000000000000000000000000000)⟩, ⟨12, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨13, (4359215377567015983031562720021036314462469/11400312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (3/1000000)⟩, ⟨2, (20980123587197913545555851780684599/1910000000000000000000000000000000000)⟩, ⟨14, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨15, (1163125077006844253193/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨9, 2⟩, ⟨2, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨16, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨17, (387708359002281417731/7296200000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨18, (1/250000)⟩, ⟨2, (33089003689562761634586927661147991/955000000000000000000000000000000000)⟩, ⟨7, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨19, (11243542411066161114199/3648100000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨12, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩]

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨20, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨9, 2⟩, ⟨9, 2⟩, ⟨5, 1⟩, ⟨21, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨7, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨2, 1⟩, ⟨22, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨23, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨22, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨2, 1⟩, ⟨7, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨24, (11243542411066161114199/3648100000000000000000000000000000000000000000000000000000000)⟩⟩]

def signNode002 : SymbolicCoverSignRefs :=
  .split signNode003 signNode004

def signNode005 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨20, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨25, (1/500000)⟩, ⟨26, (1/1000000)⟩, ⟨2, 1⟩, ⟨27, (1/955000000000000000000000000000000000)⟩⟩,
    ⟨⟨28, (23/500000)⟩, ⟨29, (23/250000)⟩, ⟨2, 1⟩, ⟨30, (23/955000000000000000000000000000000000)⟩⟩,
    ⟨⟨9, 2⟩, ⟨9, 2⟩, ⟨5, 1⟩, ⟨31, (1/1910000000000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode005

def signNode006 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨2, 1⟩, ⟨4, 1⟩, ⟨9, 2⟩, ⟨32, (1/500000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨9, 2⟩, ⟨2, 1⟩, ⟨33, (1/955000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨34, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨9, 2⟩, ⟨4, 1⟩, ⟨2, 1⟩, ⟨35, (1/1910000000000000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode006

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Cached
