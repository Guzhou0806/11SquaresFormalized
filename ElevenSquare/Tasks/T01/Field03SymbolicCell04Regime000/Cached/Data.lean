import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.Data
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

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def cache : List CachedQuarticSign :=
  [Field03SymbolicSignCache.Chunk06.entry_102_00,
   Field03SymbolicSignCache.Chunk10.entry_161_00,
   Field03SymbolicSignCache.Chunk09.entry_143_00,
   Field03SymbolicSignCache.Chunk14.entry_230_00,
   Field03SymbolicSignCache.Chunk05.entry_092_00,
   Field03SymbolicSignCache.Chunk08.entry_135_00,
   Field03SymbolicSignCache.Chunk11.entry_172_00,
   Field03SymbolicSignCache.Chunk07.entry_113_00,
   Field03SymbolicSignCache.Chunk08.entry_130_00,
   Field03SymbolicSignCache.Chunk07.entry_116_00,
   Field03SymbolicSignCache.Constants.zeroEntry,
   Field03SymbolicSignCache.Chunk12.entry_196_00,
   Field03SymbolicSignCache.Chunk12.entry_197_00,
   Field03SymbolicSignCache.Constants.oneEntry,
   Field03SymbolicSignCache.Chunk08.entry_137_00,
   Field03SymbolicSignCache.Chunk08.entry_133_00,
   Field03SymbolicSignCache.Chunk13.entry_207_00,
   Field03SymbolicSignCache.Chunk13.entry_208_00,
   Field03SymbolicSignCache.Chunk12.entry_190_00,
   Field03SymbolicSignCache.Chunk10.entry_166_00,
   Field03SymbolicSignCache.Chunk06.entry_101_00,
   Field03SymbolicSignCache.Chunk14.entry_221_00,
   Field03SymbolicSignCache.Chunk06.entry_098_00,
   Field03SymbolicSignCache.Chunk13.entry_213_00,
   Field03SymbolicSignCache.Chunk11.entry_175_00,
   Field03SymbolicSignCache.Chunk09.entry_146_00,
   Field03SymbolicSignCache.Chunk13.entry_210_00,
   Field03SymbolicSignCache.Chunk11.entry_176_00,
   Field03SymbolicSignCache.Chunk06.entry_111_00,
   Field03SymbolicSignCache.Chunk14.entry_222_00,
   Field03SymbolicSignCache.Chunk05.entry_094_00]

theorem cache_checked : SymbolicSignCache.Check cache := by
  change Field03SymbolicSignCache.Chunk06.entry_102_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_161_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_143_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_230_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_092_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_135_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_172_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_113_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_130_00.Check ∧ Field03SymbolicSignCache.Chunk07.entry_116_00.Check ∧ Field03SymbolicSignCache.Constants.zeroEntry.Check ∧ Field03SymbolicSignCache.Chunk12.entry_196_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_197_00.Check ∧ Field03SymbolicSignCache.Constants.oneEntry.Check ∧ Field03SymbolicSignCache.Chunk08.entry_137_00.Check ∧ Field03SymbolicSignCache.Chunk08.entry_133_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_207_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_208_00.Check ∧ Field03SymbolicSignCache.Chunk12.entry_190_00.Check ∧ Field03SymbolicSignCache.Chunk10.entry_166_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_101_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_221_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_098_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_213_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_175_00.Check ∧ Field03SymbolicSignCache.Chunk09.entry_146_00.Check ∧ Field03SymbolicSignCache.Chunk13.entry_210_00.Check ∧ Field03SymbolicSignCache.Chunk11.entry_176_00.Check ∧ Field03SymbolicSignCache.Chunk06.entry_111_00.Check ∧ Field03SymbolicSignCache.Chunk14.entry_222_00.Check ∧ Field03SymbolicSignCache.Chunk05.entry_094_00.Check ∧ True
  exact ⟨Field03SymbolicSignCache.Chunk06.entry_102_00_checked, Field03SymbolicSignCache.Chunk10.entry_161_00_checked, Field03SymbolicSignCache.Chunk09.entry_143_00_checked, Field03SymbolicSignCache.Chunk14.entry_230_00_checked, Field03SymbolicSignCache.Chunk05.entry_092_00_checked, Field03SymbolicSignCache.Chunk08.entry_135_00_checked, Field03SymbolicSignCache.Chunk11.entry_172_00_checked, Field03SymbolicSignCache.Chunk07.entry_113_00_checked, Field03SymbolicSignCache.Chunk08.entry_130_00_checked, Field03SymbolicSignCache.Chunk07.entry_116_00_checked, Field03SymbolicSignCache.Constants.zeroEntry_checked, Field03SymbolicSignCache.Chunk12.entry_196_00_checked, Field03SymbolicSignCache.Chunk12.entry_197_00_checked, Field03SymbolicSignCache.Constants.oneEntry_checked, Field03SymbolicSignCache.Chunk08.entry_137_00_checked, Field03SymbolicSignCache.Chunk08.entry_133_00_checked, Field03SymbolicSignCache.Chunk13.entry_207_00_checked, Field03SymbolicSignCache.Chunk13.entry_208_00_checked, Field03SymbolicSignCache.Chunk12.entry_190_00_checked, Field03SymbolicSignCache.Chunk10.entry_166_00_checked, Field03SymbolicSignCache.Chunk06.entry_101_00_checked, Field03SymbolicSignCache.Chunk14.entry_221_00_checked, Field03SymbolicSignCache.Chunk06.entry_098_00_checked, Field03SymbolicSignCache.Chunk13.entry_213_00_checked, Field03SymbolicSignCache.Chunk11.entry_175_00_checked, Field03SymbolicSignCache.Chunk09.entry_146_00_checked, Field03SymbolicSignCache.Chunk13.entry_210_00_checked, Field03SymbolicSignCache.Chunk11.entry_176_00_checked, Field03SymbolicSignCache.Chunk06.entry_111_00_checked, Field03SymbolicSignCache.Chunk14.entry_222_00_checked, Field03SymbolicSignCache.Chunk05.entry_094_00_checked, trivial⟩

def signNode002 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, (17830514181/62500000000)⟩, ⟨1, (1/500000)⟩, ⟨2, (23/250000)⟩, ⟨3, (23/477500000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨4, 2⟩, ⟨5, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨6, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (97131065203089263759485285831387891/1910000000000000000000000000000000000)⟩, ⟨7, (1/1000000)⟩, ⟨8, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨9, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 2⟩, ⟨4, 2⟩, ⟨10, 1⟩, ⟨10, 1⟩⟩,
    ⟨⟨8, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨11, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨0, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨12, (180811528186321114874026805534919308661692598193890041076586695645506475377787/435491937500000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨13, (367197/1000000)⟩, ⟨13, (58697441739775882189347354543118173/1910000000000000000000000000000000000)⟩, ⟨13, (345577383861464050670137527423/3820000000000000000000000000000)⟩, ⟨14, (1163125077006844253193/95500000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨15, (3/1000000)⟩, ⟨0, (20980123587197913545555851780684599/1910000000000000000000000000000000000)⟩, ⟨16, (387708359002281417731/3820000000000000000000000000000)⟩, ⟨17, (1163125077006844253193/7296200000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨13, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨13, (63196599378422598895493459043/3820000000000000000000000000000)⟩, ⟨13, (466359633441014238584605329874739496443199625463062337577/114003125000000000000000000000000000000000000000000000000000)⟩, ⟨18, (466359633441014238584605329874739496443199625463062337577/217745968750000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨13, (367197/1000000)⟩, ⟨13, (18858659076288984321895751381216787/955000000000000000000000000000000000)⟩, ⟨13, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨19, (33730627233198483342597/47750000000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨13, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨13, (188562042982640034999413826703/1910000000000000000000000000000)⟩, ⟨10, 1⟩, ⟨10, 1⟩⟩]

def signNode003 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨20, 1⟩, ⟨4, 2⟩, ⟨0, 1⟩, ⟨21, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨4, 2⟩, ⟨4, 2⟩, ⟨10, 1⟩, ⟨22, (1/1910000000000000000000000000000)⟩⟩,
    ⟨⟨8, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨0, 1⟩, ⟨5, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨23, (11243542411066161114199/7296200000000000000000000000000000000000000000000000000000000)⟩⟩,
    ⟨⟨0, (204386991619943324782815493233/1910000000000000000000000000000)⟩, ⟨20, 1⟩, ⟨8, (11243542411066161114199/1910000000000000000000000000000)⟩, ⟨24, (11243542411066161114199/19100000000000000000000000000000000000000000000000000)⟩⟩]

def signNode001 : SymbolicCoverSignRefs :=
  .split signNode002 signNode003

def signNode004 : SymbolicCoverSignRefs :=
  .hit [
    ⟨⟨0, 1⟩, ⟨20, 1⟩, ⟨4, 2⟩, ⟨25, (1/500000000)⟩⟩,
    ⟨⟨0, (88719/125000)⟩, ⟨26, (1/1000000)⟩, ⟨20, 1⟩, ⟨27, (1/400000000000000000000000000000000)⟩⟩,
    ⟨⟨28, (23/500000)⟩, ⟨2, (23/250000)⟩, ⟨0, 1⟩, ⟨29, (23/955000000000000000000000000000000000)⟩⟩,
    ⟨⟨4, 2⟩, ⟨4, 2⟩, ⟨10, 1⟩, ⟨30, (1/1910000000000000000000000000000)⟩⟩]

def signNode000 : SymbolicCoverSignRefs :=
  .split signNode001 signNode004

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.Cached
