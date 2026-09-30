import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window067.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window067.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window067.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window067.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window067.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window067
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-173431483117976703253419723021/3820000000000000000000000000000), (-55592369876637204828989733211/1910000000000000000000000000000), (-3678135085325593463954171510746808955170095444735940796242744119206773/44299552016515600000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-173431483117976703253419723021/3820000000000000000000000000000), (-55592369876637204828989733211/1910000000000000000000000000000), (-3678135085325593463954171510746808955170095444735940796242744119206773/44299552016515600000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-387708359002281417731/4000000000000000000000), (-271525087292028299883516527423/3820000000000000000000000000000), (-10646232125078152392742162084995000493828122192905550610306967/57983706827900000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(-387708359002281417731/4000000000000000000000), (-271525087292028299883516527423/3820000000000000000000000000000), (-10646232125078152392742162084995000493828122192905550610306967/57983706827900000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-5248/5777), (2415/5777), (-2201471661829180006831597975578967243573/2319348273116000000000000000000000000000)⟩ :: nodeSource001 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource001, nodeSource007]
  change node007.Check (baselineFlip ⟨(-5248/5777), (2415/5777), (-2201471661829180006831597975578967243573/2319348273116000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node007_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-2415/5777), (-5248/5777), (-210450233582497608085593137411480706183/181199083837187500000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-2415/5777), (-5248/5777), (-210450233582497608085593137411480706183/181199083837187500000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa [nodeSource000] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window067
