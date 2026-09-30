import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.Data
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

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk04.entry_068_00,
   Field03SymbolicSignCache.Chunk01.entry_026_00,
   Field03SymbolicSignCache.Chunk10.entry_160_00,
   Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk07.entry_113_00,
   Field03SymbolicSignCache.Chunk12.entry_192_00,
   Field03SymbolicSignCache.Chunk00.entry_002_00,
   Field03SymbolicSignCache.Chunk13.entry_216_00,
   Field03SymbolicSignCache.Chunk05.entry_090_00,
   Field03SymbolicSignCache.Chunk05.entry_089_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk02.entry_035_00,
   Field03SymbolicSignCache.Chunk00.entry_004_00,
   Field03SymbolicSignCache.Chunk01.entry_019_00,
   Field03SymbolicSignCache.Chunk05.entry_084_00,
   Field03SymbolicSignCache.Chunk12.entry_189_00,
   Field03SymbolicSignCache.Chunk02.entry_038_00,
   Field03SymbolicSignCache.Chunk03.entry_050_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk00.entry_011_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk14.entry_231_00,
   Field03SymbolicSignCache.Chunk01.entry_025_00,
   Field03SymbolicSignCache.Chunk09.entry_146_00,
   Field03SymbolicSignCache.Chunk09.entry_143_00,
   Field03SymbolicSignCache.Chunk01.entry_017_00,
   Field03SymbolicSignCache.Chunk11.entry_183_00,
   Field03SymbolicSignCache.Chunk08.entry_139_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk04.entry_068_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_026_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_160_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk07.entry_113_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_192_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_002_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_216_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_090_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_089_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk02.entry_035_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_004_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_019_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_084_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_189_00.Check ∧ Field03SymbolicSignCache.Chunk02.entry_038_00.Check ∧ Field03SymbolicSignCache.Chunk03.entry_050_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk00.entry_011_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_231_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_025_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_146_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_143_00.Check ∧ Field03SymbolicSignCache.Chunk01.entry_017_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_183_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_139_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk04.entry_068_00_checked, Field03SymbolicSignCache.Chunk01.entry_026_00_checked, Field03SymbolicSignCache.Chunk10.entry_160_00_checked, Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk07.entry_113_00_checked, Field03SymbolicSignCache.Chunk12.entry_192_00_checked, Field03SymbolicSignCache.Chunk00.entry_002_00_checked, Field03SymbolicSignCache.Chunk13.entry_216_00_checked, Field03SymbolicSignCache.Chunk05.entry_090_00_checked, Field03SymbolicSignCache.Chunk05.entry_089_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk02.entry_035_00_checked, Field03SymbolicSignCache.Chunk00.entry_004_00_checked, Field03SymbolicSignCache.Chunk01.entry_019_00_checked, Field03SymbolicSignCache.Chunk05.entry_084_00_checked, Field03SymbolicSignCache.Chunk12.entry_189_00_checked, Field03SymbolicSignCache.Chunk02.entry_038_00_checked, Field03SymbolicSignCache.Chunk03.entry_050_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk00.entry_011_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk14.entry_231_00_checked, Field03SymbolicSignCache.Chunk01.entry_025_00_checked, Field03SymbolicSignCache.Chunk09.entry_146_00_checked, Field03SymbolicSignCache.Chunk09.entry_143_00_checked, Field03SymbolicSignCache.Chunk01.entry_017_00_checked, Field03SymbolicSignCache.Chunk11.entry_183_00_checked, Field03SymbolicSignCache.Chunk08.entry_139_00_checked, trivial⟩

def signNode002 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, (87273705095204290923012079059236267/955000000000000000000000000000000000)⟩, ⟨1, (1/500000)⟩, ⟨2, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨3, (11243542411066161114199/3648100000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, (52819/100000)⟩, ⟨6, (1/1000000)⟩, ⟨4, 1⟩, ⟨7, (1/191000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (17830514181/62500000000)⟩, ⟨6, (1/1000000)⟩, ⟨8, (23/500000)⟩, ⟨9, (23/955000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨2, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨10, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨0, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨11, (180811528186321114874026805534919308661692598193890041076586695645506475377787/435491937500000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (367197/1000000)⟩, ⟨12, (58697441739775882189347354543118173/1910000000000000000000000000000000000)⟩, ⟨12, (345577383861464050670137527423/3820000000000000000000000000000)⟩, ⟨13, (1163125077006844253193/95500000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨14, (3/1000000)⟩, ⟨0, (20980123587197913545555851780684599/1910000000000000000000000000000000000)⟩, ⟨15, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨16, (1163125077006844253193/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨12, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨12, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨17, (466359633441014238584605329874739496443199625463062337577/217745968750000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (367197/1000000)⟩, ⟨12, (18858659076288984321895751381216787/955000000000000000000000000000000000)⟩, ⟨12, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨18, (33730627233198483342597/47750000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨12, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨12, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩]

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨19, (1/3820000000000000000000000000000)⟩⟩,
    ⟨⟨2, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨0, 1⟩, ⟨20, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨21, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨22, 2⟩, ⟨2, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨23, (11243542411066161114199/9550000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨4, 1⟩, ⟨20, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨24, (11243542411066161114199/19100000000000000000000000000000000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode003

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨4, 1⟩, ⟨22, 2⟩, ⟨25, (1/500000000)⟩⟩,
    ⟨⟨26, (23/250000)⟩, ⟨8, (23/500000)⟩, ⟨0, 1⟩, ⟨27, (23/1910000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩, ⟨28, (1/3820000000000000000000000000000)⟩⟩,
    ⟨⟨22, 2⟩, ⟨4, 1⟩, ⟨0, 1⟩, ⟨29, (1/3820000000000000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode004

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.Cached
