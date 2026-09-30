import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCachedCover
import ElevenSquare.Tasks.T01.Field03SymbolicSignCache.Chunk00
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

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk00.entry_004_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk09.entry_153_00,
   Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk07.entry_113_00,
   Field03SymbolicSignCache.Chunk12.entry_192_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk12.entry_197_00,
   Field03SymbolicSignCache.Chunk04.entry_067_00,
   Field03SymbolicSignCache.Chunk08.entry_133_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk00.entry_013_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk02.entry_040_00,
   Field03SymbolicSignCache.Chunk10.entry_166_00,
   Field03SymbolicSignCache.Chunk06.entry_108_00,
   Field03SymbolicSignCache.Chunk06.entry_099_00,
   Field03SymbolicSignCache.Chunk08.entry_135_00,
   Field03SymbolicSignCache.Chunk12.entry_200_00,
   Field03SymbolicSignCache.Chunk03.entry_057_00,
   Field03SymbolicSignCache.Chunk03.entry_048_00,
   Field03SymbolicSignCache.Chunk09.entry_158_00,
   Field03SymbolicSignCache.Chunk13.entry_209_00,
   Field03SymbolicSignCache.Chunk05.entry_085_00,
   Field03SymbolicSignCache.Chunk06.entry_111_00,
   Field03SymbolicSignCache.Chunk09.entry_143_00,
   Field03SymbolicSignCache.Chunk14.entry_222_00,
   Field03SymbolicSignCache.Chunk05.entry_094_00,
   Field03SymbolicSignCache.Chunk06.entry_110_00,
   Field03SymbolicSignCache.Chunk08.entry_134_00,
   Field03SymbolicSignCache.Chunk00.entry_005_00,
   Field03SymbolicSignCache.Chunk09.entry_157_00,
   Field03SymbolicSignCache.Chunk07.entry_123_00,
   Field03SymbolicSignCache.Chunk12.entry_188_01]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_004_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_153_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk07.entry_113_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_192_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_197_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_067_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_133_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_013_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk02.entry_040_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_166_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_108_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_099_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_135_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_200_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_057_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_048_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_158_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_209_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_085_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_111_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_143_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_222_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_094_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_110_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_134_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_005_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_157_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_123_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_188_01.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk00.entry_004_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk09.entry_153_00_checked, Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk07.entry_113_00_checked, Field03SymbolicSignCache.Chunk12.entry_192_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk12.entry_197_00_checked, Field03SymbolicSignCache.Chunk04.entry_067_00_checked, Field03SymbolicSignCache.Chunk08.entry_133_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk00.entry_013_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk02.entry_040_00_checked, Field03SymbolicSignCache.Chunk10.entry_166_00_checked, Field03SymbolicSignCache.Chunk06.entry_108_00_checked, Field03SymbolicSignCache.Chunk06.entry_099_00_checked, Field03SymbolicSignCache.Chunk08.entry_135_00_checked, Field03SymbolicSignCache.Chunk12.entry_200_00_checked, Field03SymbolicSignCache.Chunk03.entry_057_00_checked, Field03SymbolicSignCache.Chunk03.entry_048_00_checked, Field03SymbolicSignCache.Chunk09.entry_158_00_checked, Field03SymbolicSignCache.Chunk13.entry_209_00_checked, Field03SymbolicSignCache.Chunk05.entry_085_00_checked, Field03SymbolicSignCache.Chunk06.entry_111_00_checked, Field03SymbolicSignCache.Chunk09.entry_143_00_checked, Field03SymbolicSignCache.Chunk14.entry_222_00_checked, Field03SymbolicSignCache.Chunk05.entry_094_00_checked, Field03SymbolicSignCache.Chunk06.entry_110_00_checked, Field03SymbolicSignCache.Chunk08.entry_134_00_checked, Field03SymbolicSignCache.Chunk00.entry_005_00_checked, Field03SymbolicSignCache.Chunk09.entry_157_00_checked, Field03SymbolicSignCache.Chunk07.entry_123_00_checked, Field03SymbolicSignCache.Chunk12.entry_188_01_checked, trivial⟩

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, (367197/1000000)⟩, ⟨1, (3/1000000)⟩, ⟨2, 2⟩, ⟨3, (3/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, (52819/100000)⟩, ⟨6, (1/1000000)⟩, ⟨4, 1⟩, ⟨7, (1/191000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨2, 2⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨8, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨9, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨0, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨10, (180811528186321114874026805534919308661692598193890041076586695645506475377787/435491937500000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨6, (1/1000000)⟩, ⟨0, (87096559311764346689203612327141981/3820000000000000000000000000000000000)⟩, ⟨9, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨11, (387708359002281417731/14592400000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (3/1000000)⟩, ⟨0, (20980123587197913545555851780684599/1910000000000000000000000000000000000)⟩, ⟨13, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨14, (1163125077006844253193/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨15, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨15, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨15, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨16, (13077646132701047949094688160063108943387407/217745968750000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨15, (367197/1000000)⟩, ⟨15, (18858659076288984321895751381216787/955000000000000000000000000000000000)⟩, ⟨15, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨17, (33730627233198483342597/47750000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨15, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨15, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩]

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨18, (3/1910000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨2, 2⟩, ⟨5, 1⟩, ⟨19, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨8, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨0, 1⟩, ⟨20, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨21, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨20, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨0, 1⟩, ⟨8, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨22, (11243542411066161114199/3648100000000000000000000000000000000000000000000000000000000)⟩⟩]

def signNode002 : SymbolicCoverSignRefs :=
  .split signNode003 signNode004

def signNode005 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨23, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨24, (1/500000)⟩, ⟨25, (1/500000)⟩, ⟨0, 1⟩, ⟨26, (1/955000000000000000000000000000000000)⟩⟩,
    ⟨⟨27, (23/500000)⟩, ⟨28, (23/250000)⟩, ⟨0, 1⟩, ⟨29, (23/955000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨2, 2⟩, ⟨5, 1⟩, ⟨30, (1/1910000000000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode005

def signNode006 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨4, 1⟩, ⟨2, 2⟩, ⟨31, (1/500000000)⟩⟩,
    ⟨⟨32, (3/1000000)⟩, ⟨33, (3/1000000)⟩, ⟨0, 1⟩, ⟨34, (3/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨35, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨2, 2⟩, ⟨4, 1⟩, ⟨0, 1⟩, ⟨36, (1/1910000000000000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode006

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Cached
