import ElevenSquare.Tasks.T06.ConcreteTaylorRow00
import ElevenSquare.Tasks.T06.ConcreteTaylorRow01
import ElevenSquare.Tasks.T06.ConcreteTaylorRow02
import ElevenSquare.Tasks.T06.ConcreteTaylorRow03
import ElevenSquare.Tasks.T06.ConcreteTaylorRow04
import ElevenSquare.Tasks.T06.ConcreteTaylorRow05
import ElevenSquare.Tasks.T06.ConcreteTaylorRow06
import ElevenSquare.Tasks.T06.ConcreteTaylorRow07
import ElevenSquare.Tasks.T06.ConcreteTaylorRow08
import ElevenSquare.Tasks.T06.ConcreteTaylorRow09
import ElevenSquare.Tasks.T06.ConcreteTaylorRow10
import ElevenSquare.Tasks.T06.ConcreteTaylorRow11
import ElevenSquare.Tasks.T06.ConcreteTaylorRow12
import ElevenSquare.Tasks.T06.ConcreteTaylorRow13
import ElevenSquare.Tasks.T06.ConcreteTaylorRow14
import ElevenSquare.Tasks.T06.ConcreteTaylorRow15
import ElevenSquare.Tasks.T06.ConcreteTaylorRow16
import ElevenSquare.Tasks.T06.ConcreteTaylorRow17
import ElevenSquare.Tasks.T06.ConcreteTaylorRow18
import ElevenSquare.Tasks.T06.ConcreteTaylorRow19
import ElevenSquare.Tasks.T06.ConcreteTaylorRow20
import ElevenSquare.Tasks.T06.ConcreteTaylorRow21
import ElevenSquare.Tasks.T06.ConcreteTaylorRow22
import ElevenSquare.Tasks.T06.ConcreteTaylorRow23
import ElevenSquare.Tasks.T06.ConcreteTaylorRow24
import ElevenSquare.Tasks.T06.ConcreteTaylorRow25
import ElevenSquare.Tasks.T06.ConcreteTaylorRow26
import ElevenSquare.Tasks.T06.ConcreteTaylorRow27
import ElevenSquare.Tasks.T06.ConcreteTaylorRow28
import ElevenSquare.Tasks.T06.ConcreteTaylorRow29
import ElevenSquare.Tasks.T06.ConcreteTaylorRow30
import ElevenSquare.Tasks.T06.ConcreteTaylorRow31
import ElevenSquare.Tasks.T06.ConcreteTaylorRow32
import ElevenSquare.Tasks.T06.ConcreteTaylorRow33
import ElevenSquare.Tasks.T06.ConcreteTaylorRow34
import ElevenSquare.Tasks.T06.ConcreteTaylorRow35
import ElevenSquare.Tasks.T06.ConcreteTaylorRow36
import ElevenSquare.Tasks.T06.ConcreteTaylorRow37
import ElevenSquare.Tasks.T06.ConcreteTaylorRow38
import ElevenSquare.Tasks.T06.ConcreteTaylorRow39
import ElevenSquare.Tasks.T06.ConcreteTaylorRow40
import ElevenSquare.Tasks.T06.ConcreteTaylorRow41
import ElevenSquare.Tasks.T06.ConcreteTaylorRow42
import ElevenSquare.Tasks.T06.ConcreteTaylorRow43
import ElevenSquare.Tasks.T06.ConcreteTaylorRow44
import ElevenSquare.Tasks.T06.ConcreteTaylorRow45
import ElevenSquare.Tasks.T06.ConcreteTaylorRow46
import ElevenSquare.Tasks.T06.ConcreteTaylorRow47
import ElevenSquare.Tasks.T06.ConcreteTaylorRow48
import ElevenSquare.Tasks.T06.ConcreteTaylorRow49
import ElevenSquare.Tasks.T06.ConcreteTaylorRow50
import ElevenSquare.Tasks.T06.ConcreteTaylorRow51
import ElevenSquare.Tasks.T06.ConcreteTaylorRow52
import ElevenSquare.Tasks.T06.ConcreteTaylorRow53
import ElevenSquare.Tasks.T06.ConcreteTaylorRow54
import ElevenSquare.Tasks.T06.ConcreteTaylorRow55

namespace ElevenSquare.Tasks.T06
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_row_curvature (i : Fin 56) (g : Gap) (hg : g ∈ rowAliases i) :
    gapRectangleCurvature constructionSquare focusedRadii g ≤ (rowCurvatures i : ℝ) := by
  fin_cases i
  · exact concreteRow00_curvature g hg
  · exact concreteRow01_curvature g hg
  · exact concreteRow02_curvature g hg
  · exact concreteRow03_curvature g hg
  · exact concreteRow04_curvature g hg
  · exact concreteRow05_curvature g hg
  · exact concreteRow06_curvature g hg
  · exact concreteRow07_curvature g hg
  · exact concreteRow08_curvature g hg
  · exact concreteRow09_curvature g hg
  · exact concreteRow10_curvature g hg
  · exact concreteRow11_curvature g hg
  · exact concreteRow12_curvature g hg
  · exact concreteRow13_curvature g hg
  · exact concreteRow14_curvature g hg
  · exact concreteRow15_curvature g hg
  · exact concreteRow16_curvature g hg
  · exact concreteRow17_curvature g hg
  · exact concreteRow18_curvature g hg
  · exact concreteRow19_curvature g hg
  · exact concreteRow20_curvature g hg
  · exact concreteRow21_curvature g hg
  · exact concreteRow22_curvature g hg
  · exact concreteRow23_curvature g hg
  · exact concreteRow24_curvature g hg
  · exact concreteRow25_curvature g hg
  · exact concreteRow26_curvature g hg
  · exact concreteRow27_curvature g hg
  · exact concreteRow28_curvature g hg
  · exact concreteRow29_curvature g hg
  · exact concreteRow30_curvature g hg
  · exact concreteRow31_curvature g hg
  · exact concreteRow32_curvature g hg
  · exact concreteRow33_curvature g hg
  · exact concreteRow34_curvature g hg
  · exact concreteRow35_curvature g hg
  · exact concreteRow36_curvature g hg
  · exact concreteRow37_curvature g hg
  · exact concreteRow38_curvature g hg
  · exact concreteRow39_curvature g hg
  · exact concreteRow40_curvature g hg
  · exact concreteRow41_curvature g hg
  · exact concreteRow42_curvature g hg
  · exact concreteRow43_curvature g hg
  · exact concreteRow44_curvature g hg
  · exact concreteRow45_curvature g hg
  · exact concreteRow46_curvature g hg
  · exact concreteRow47_curvature g hg
  · exact concreteRow48_curvature g hg
  · exact concreteRow49_curvature g hg
  · exact concreteRow50_curvature g hg
  · exact concreteRow51_curvature g hg
  · exact concreteRow52_curvature g hg
  · exact concreteRow53_curvature g hg
  · exact concreteRow54_curvature g hg
  · exact concreteRow55_curvature g hg

end
end ElevenSquare.Tasks.T06
