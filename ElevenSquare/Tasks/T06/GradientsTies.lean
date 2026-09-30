import ElevenSquare.Tasks.T06.GradientsRow00
import ElevenSquare.Tasks.T06.GradientsRow01
import ElevenSquare.Tasks.T06.GradientsRow02
import ElevenSquare.Tasks.T06.GradientsRow03
import ElevenSquare.Tasks.T06.GradientsRow04
import ElevenSquare.Tasks.T06.GradientsRow05
import ElevenSquare.Tasks.T06.GradientsRow06
import ElevenSquare.Tasks.T06.GradientsRow07
import ElevenSquare.Tasks.T06.GradientsRow08
import ElevenSquare.Tasks.T06.GradientsRow09
import ElevenSquare.Tasks.T06.GradientsRow10
import ElevenSquare.Tasks.T06.GradientsRow11
import ElevenSquare.Tasks.T06.GradientsRow12
import ElevenSquare.Tasks.T06.GradientsRow13
import ElevenSquare.Tasks.T06.GradientsRow14
import ElevenSquare.Tasks.T06.GradientsRow15
import ElevenSquare.Tasks.T06.GradientsRow16
import ElevenSquare.Tasks.T06.GradientsRow17
import ElevenSquare.Tasks.T06.GradientsRow18
import ElevenSquare.Tasks.T06.GradientsRow19
import ElevenSquare.Tasks.T06.GradientsRow20
import ElevenSquare.Tasks.T06.GradientsRow21
import ElevenSquare.Tasks.T06.GradientsRow22
import ElevenSquare.Tasks.T06.GradientsRow23
import ElevenSquare.Tasks.T06.GradientsRow24
import ElevenSquare.Tasks.T06.GradientsRow25
import ElevenSquare.Tasks.T06.GradientsRow26
import ElevenSquare.Tasks.T06.GradientsRow27
import ElevenSquare.Tasks.T06.GradientsRow28
import ElevenSquare.Tasks.T06.GradientsRow29
import ElevenSquare.Tasks.T06.GradientsRow30
import ElevenSquare.Tasks.T06.GradientsRow31
import ElevenSquare.Tasks.T06.GradientsRow32
import ElevenSquare.Tasks.T06.GradientsRow33
import ElevenSquare.Tasks.T06.GradientsRow34
import ElevenSquare.Tasks.T06.GradientsRow35
import ElevenSquare.Tasks.T06.GradientsRow36
import ElevenSquare.Tasks.T06.GradientsRow37
import ElevenSquare.Tasks.T06.GradientsRow38
import ElevenSquare.Tasks.T06.GradientsRow39
import ElevenSquare.Tasks.T06.GradientsRow40
import ElevenSquare.Tasks.T06.GradientsRow41
import ElevenSquare.Tasks.T06.GradientsRow42
import ElevenSquare.Tasks.T06.GradientsRow43
import ElevenSquare.Tasks.T06.GradientsRow44
import ElevenSquare.Tasks.T06.GradientsRow45
import ElevenSquare.Tasks.T06.GradientsRow46
import ElevenSquare.Tasks.T06.GradientsRow47
import ElevenSquare.Tasks.T06.GradientsRow48
import ElevenSquare.Tasks.T06.GradientsRow49
import ElevenSquare.Tasks.T06.GradientsRow50
import ElevenSquare.Tasks.T06.GradientsRow51
import ElevenSquare.Tasks.T06.GradientsRow52
import ElevenSquare.Tasks.T06.GradientsRow53
import ElevenSquare.Tasks.T06.GradientsRow54
import ElevenSquare.Tasks.T06.GradientsRow55

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem row_aliases_tied (r : Fin 56) (g : Gap) (hg : g ∈ rowAliases r) :
    gapValue T constructionSquare g 0 = 0 ∧ gapGradient T constructionSquare g = polynomialGradient r := by
  fin_cases r
  · exact row00_aliases_tied g hg
  · exact row01_aliases_tied g hg
  · exact row02_aliases_tied g hg
  · exact row03_aliases_tied g hg
  · exact row04_aliases_tied g hg
  · exact row05_aliases_tied g hg
  · exact row06_aliases_tied g hg
  · exact row07_aliases_tied g hg
  · exact row08_aliases_tied g hg
  · exact row09_aliases_tied g hg
  · exact row10_aliases_tied g hg
  · exact row11_aliases_tied g hg
  · exact row12_aliases_tied g hg
  · exact row13_aliases_tied g hg
  · exact row14_aliases_tied g hg
  · exact row15_aliases_tied g hg
  · exact row16_aliases_tied g hg
  · exact row17_aliases_tied g hg
  · exact row18_aliases_tied g hg
  · exact row19_aliases_tied g hg
  · exact row20_aliases_tied g hg
  · exact row21_aliases_tied g hg
  · exact row22_aliases_tied g hg
  · exact row23_aliases_tied g hg
  · exact row24_aliases_tied g hg
  · exact row25_aliases_tied g hg
  · exact row26_aliases_tied g hg
  · exact row27_aliases_tied g hg
  · exact row28_aliases_tied g hg
  · exact row29_aliases_tied g hg
  · exact row30_aliases_tied g hg
  · exact row31_aliases_tied g hg
  · exact row32_aliases_tied g hg
  · exact row33_aliases_tied g hg
  · exact row34_aliases_tied g hg
  · exact row35_aliases_tied g hg
  · exact row36_aliases_tied g hg
  · exact row37_aliases_tied g hg
  · exact row38_aliases_tied g hg
  · exact row39_aliases_tied g hg
  · exact row40_aliases_tied g hg
  · exact row41_aliases_tied g hg
  · exact row42_aliases_tied g hg
  · exact row43_aliases_tied g hg
  · exact row44_aliases_tied g hg
  · exact row45_aliases_tied g hg
  · exact row46_aliases_tied g hg
  · exact row47_aliases_tied g hg
  · exact row48_aliases_tied g hg
  · exact row49_aliases_tied g hg
  · exact row50_aliases_tied g hg
  · exact row51_aliases_tied g hg
  · exact row52_aliases_tied g hg
  · exact row53_aliases_tied g hg
  · exact row54_aliases_tied g hg
  · exact row55_aliases_tied g hg

theorem representative_gradient (r : Fin 56) :
    gapGradient T constructionSquare (representatives r) = polynomialGradient r :=
  (row_aliases_tied r (representatives r) (representative_mem_aliases r)).2

theorem row_alias_gradient_eq (r : Fin 56) (g : Gap) (hg : g ∈ rowAliases r) :
    gapGradient T constructionSquare g = gapGradient T constructionSquare (representatives r) := by
  rw [(row_aliases_tied r g hg).2, representative_gradient]

end
end ElevenSquare.Tasks.T06
