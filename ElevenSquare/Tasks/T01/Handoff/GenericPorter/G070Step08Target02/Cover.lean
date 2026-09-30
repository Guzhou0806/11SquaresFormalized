import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def src0 : SymbolicFacet := ⟨⟨(-1 : ℚ), (0 : ℚ), (-1 : ℚ)⟩, ⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(-1/2 : ℚ), (-1 : ℚ), (1/2 : ℚ)⟩⟩
def src1 : SymbolicFacet := ⟨⟨(1 : ℚ), (0 : ℚ), (1 : ℚ)⟩, ⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(337708359002281417731/100000000000000000000 : ℚ), (-1 : ℚ), (437708359002281417731/100000000000000000000 : ℚ)⟩⟩
def src2 : SymbolicFacet := ⟨⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(-1 : ℚ), (0 : ℚ), (-1 : ℚ)⟩, ⟨(-1/2 : ℚ), (-1 : ℚ), (1/2 : ℚ)⟩⟩
def src3 : SymbolicFacet := ⟨⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(1 : ℚ), (0 : ℚ), (1 : ℚ)⟩, ⟨(337708359002281417731/100000000000000000000 : ℚ), (-1 : ℚ), (437708359002281417731/100000000000000000000 : ℚ)⟩⟩
def src4 : SymbolicFacet := ⟨⟨(-1 : ℚ), (0 : ℚ), (-1 : ℚ)⟩, ⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(-1/2 : ℚ), (0 : ℚ), (-1/2 : ℚ)⟩⟩
def src5 : SymbolicFacet := ⟨⟨(1 : ℚ), (0 : ℚ), (1 : ℚ)⟩, ⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(337708359002281417731/100000000000000000000 : ℚ), (0 : ℚ), (337708359002281417731/100000000000000000000 : ℚ)⟩⟩
def src6 : SymbolicFacet := ⟨⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(-1 : ℚ), (0 : ℚ), (-1 : ℚ)⟩, ⟨(-1/2 : ℚ), (0 : ℚ), (-1/2 : ℚ)⟩⟩
def src7 : SymbolicFacet := ⟨⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(1 : ℚ), (0 : ℚ), (1 : ℚ)⟩, ⟨(337708359002281417731/100000000000000000000 : ℚ), (0 : ℚ), (337708359002281417731/100000000000000000000 : ℚ)⟩⟩
def src8 : SymbolicFacet := ⟨⟨(-1521141/1000000 : ℚ), (0 : ℚ), (-1521141/1000000 : ℚ)⟩, ⟨(60229/1000000 : ℚ), (0 : ℚ), (60229/1000000 : ℚ)⟩, ⟨(-11335278793974273733773665481669/4000000000000000000000000000000 : ℚ), (0 : ℚ), (-11335278793974273733773665481669/4000000000000000000000000000000 : ℚ)⟩⟩
def src9 : SymbolicFacet := ⟨⟨(-984719/1000000 : ℚ), (0 : ℚ), (-984719/1000000 : ℚ)⟩, ⟨(-57301/500000 : ℚ), (0 : ℚ), (-57301/500000 : ℚ)⟩, ⟨(-931556993845037328070121787369471/400000000000000000000000000000000 : ℚ), (0 : ℚ), (-931556993845037328070121787369471/400000000000000000000000000000000 : ℚ)⟩⟩
def src10 : SymbolicFacet := ⟨⟨(-11597/25000 : ℚ), (0 : ℚ), (-11597/25000 : ℚ)⟩, ⟨(2247/31250 : ℚ), (0 : ℚ), (2247/31250 : ℚ)⟩, ⟨(-1171422739114251067047341103669/1000000000000000000000000000000 : ℚ), (0 : ℚ), (-1171422739114251067047341103669/1000000000000000000000000000000 : ℚ)⟩⟩
def src11 : SymbolicFacet := ⟨⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩, ⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩⟩
def src12 : SymbolicFacet := ⟨⟨(-762471/500000 : ℚ), (0 : ℚ), (-762471/500000 : ℚ)⟩, ⟨(11903/20000 : ℚ), (0 : ℚ), (11903/20000 : ℚ)⟩, ⟨(-215902172580243867443288127759777/100000000000000000000000000000000 : ℚ), (0 : ℚ), (-215902172580243867443288127759777/100000000000000000000000000000000 : ℚ)⟩⟩
def src13 : SymbolicFacet := ⟨⟨(-247203/250000 : ℚ), (0 : ℚ), (-247203/250000 : ℚ)⟩, ⟨(210129/500000 : ℚ), (0 : ℚ), (210129/500000 : ℚ)⟩, ⟨(-179210444878683087161629418669199/100000000000000000000000000000000 : ℚ), (0 : ℚ), (-179210444878683087161629418669199/100000000000000000000000000000000 : ℚ)⟩⟩
def src14 : SymbolicFacet := ⟨⟨(-460609/1000000 : ℚ), (0 : ℚ), (-460609/1000000 : ℚ)⟩, ⟨(626437/1000000 : ℚ), (0 : ℚ), (626437/1000000 : ℚ)⟩, ⟨(-44399277591299476346321727011533/100000000000000000000000000000000 : ℚ), (0 : ℚ), (-44399277591299476346321727011533/100000000000000000000000000000000 : ℚ)⟩⟩
def src15 : SymbolicFacet := ⟨⟨(50633/1000000 : ℚ), (0 : ℚ), (50633/1000000 : ℚ)⟩, ⟨(116361/250000 : ℚ), (0 : ℚ), (116361/250000 : ℚ)⟩, ⟨(271784803409596628652833589934757/400000000000000000000000000000000 : ℚ), (0 : ℚ), (271784803409596628652833589934757/400000000000000000000000000000000 : ℚ)⟩⟩
def src16 : SymbolicFacet := ⟨⟨(-1512879/1000000 : ℚ), (0 : ℚ), (-1512879/1000000 : ℚ)⟩, ⟨(56167/50000 : ℚ), (0 : ℚ), (56167/50000 : ℚ)⟩, ⟨(-430444983082823548146921002065243/400000000000000000000000000000000 : ℚ), (0 : ℚ), (-430444983082823548146921002065243/400000000000000000000000000000000 : ℚ)⟩⟩
def src17 : SymbolicFacet := ⟨⟨(-1001637/1000000 : ℚ), (0 : ℚ), (-1001637/1000000 : ℚ)⟩, ⟨(962347/1000000 : ℚ), (0 : ℚ), (962347/1000000 : ℚ)⟩, ⟨(-84162259182214456267395356011533/100000000000000000000000000000000 : ℚ), (0 : ℚ), (-84162259182214456267395356011533/100000000000000000000000000000000 : ℚ)⟩⟩
def src18 : SymbolicFacet := ⟨⟨(-236717/500000 : ℚ), (0 : ℚ), (-236717/500000 : ℚ)⟩, ⟨(584263/500000 : ℚ), (0 : ℚ), (584263/500000 : ℚ)⟩, ⟨(65752613631215365033424194330801/100000000000000000000000000000000 : ℚ), (0 : ℚ), (65752613631215365033424194330801/100000000000000000000000000000000 : ℚ)⟩⟩
def src19 : SymbolicFacet := ⟨⟨(7837/125000 : ℚ), (0 : ℚ), (7837/125000 : ℚ)⟩, ⟨(496817/500000 : ℚ), (0 : ℚ), (496817/500000 : ℚ)⟩, ⟨(169115878118920719530076463240223/100000000000000000000000000000000 : ℚ), (0 : ℚ), (169115878118920719530076463240223/100000000000000000000000000000000 : ℚ)⟩⟩
def src20 : SymbolicFacet := ⟨⟨(-731123/500000 : ℚ), (0 : ℚ), (-731123/500000 : ℚ)⟩, ⟨(99299/62500 : ℚ), (0 : ℚ), (99299/62500 : ℚ)⟩, ⟨(24529920165715343018422639/100000000000000000000000000 : ℚ), (0 : ℚ), (24529920165715343018422639/100000000000000000000000000 : ℚ)⟩⟩
def src21 : SymbolicFacet := ⟨⟨(-499183/500000 : ℚ), (0 : ℚ), (-499183/500000 : ℚ)⟩, ⟨(18961/12500 : ℚ), (0 : ℚ), (18961/12500 : ℚ)⟩, ⟨(593600179825684973102149846331/1000000000000000000000000000000 : ℚ), (0 : ℚ), (593600179825684973102149846331/1000000000000000000000000000000 : ℚ)⟩⟩
def src22 : SymbolicFacet := ⟨⟨(-477527/1000000 : ℚ), (0 : ℚ), (-477527/1000000 : ℚ)⟩, ⟨(851693/500000 : ℚ), (0 : ℚ), (851693/500000 : ℚ)⟩, ⟨(871426450524812085689411372630529/400000000000000000000000000000000 : ℚ), (0 : ℚ), (871426450524812085689411372630529/400000000000000000000000000000000 : ℚ)⟩⟩
def src23 : SymbolicFacet := ⟨⟨(11779/200000 : ℚ), (0 : ℚ), (11779/200000 : ℚ)⟩, ⟨(305711/200000 : ℚ), (0 : ℚ), (305711/200000 : ℚ)⟩, ⟨(12302229779323978008572466958331/4000000000000000000000000000000 : ℚ), (0 : ℚ), (12302229779323978008572466958331/4000000000000000000000000000000 : ℚ)⟩⟩
def source : List SymbolicFacet := [src0, src1, src2, src3, src4, src5, src6, src7, src8, src9, src10, src11, src12, src13, src14, src15, src16, src17, src18, src19, src20, src21, src22, src23]

theorem source_matches : symbolicWallScaledSlab (3 : Fin 16) = source := by
  have hrange : (List.finRange 16 : List (Fin 16)) =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  have hs0 : baselineRationalSite (0 : Fin 16) = ((104991/1000000 : ℚ), (265837/2000000 : ℚ)) := by rfl
  have hs1 : baselineRationalSite (1 : Fin 16) = ((186601/500000 : ℚ), (45503/1000000 : ℚ)) := by rfl
  have hs2 : baselineRationalSite (2 : Fin 16) = ((1267243/2000000 : ℚ), (34689/250000 : ℚ)) := by rfl
  have hs3 : baselineRationalSite (3 : Fin 16) = ((1731123/2000000 : ℚ), (25701/250000 : ℚ)) := by rfl
  have hs4 : baselineRationalSite (4 : Fin 16) = ((206181/2000000 : ℚ), (400379/1000000 : ℚ)) := by rfl
  have hs5 : baselineRationalSite (5 : Fin 16) = ((742311/2000000 : ℚ), (312933/1000000 : ℚ)) := by rfl
  have hs6 : baselineRationalSite (6 : Fin 16) = ((635257/1000000 : ℚ), (166409/400000 : ℚ)) := by rfl
  have hs7 : baselineRationalSite (7 : Fin 16) = ((445439/500000 : ℚ), (167763/500000 : ℚ)) := by rfl
  have hs8 : baselineRationalSite (8 : Fin 16) = ((54561/500000 : ℚ), (332237/500000 : ℚ)) := by rfl
  have hs9 : baselineRationalSite (9 : Fin 16) = ((364743/1000000 : ℚ), (233591/400000 : ℚ)) := by rfl
  have hs10 : baselineRationalSite (10 : Fin 16) = ((1257689/2000000 : ℚ), (687067/1000000 : ℚ)) := by rfl
  have hs11 : baselineRationalSite (11 : Fin 16) = ((1793819/2000000 : ℚ), (599621/1000000 : ℚ)) := by rfl
  have hs12 : baselineRationalSite (12 : Fin 16) = ((268877/2000000 : ℚ), (224299/250000 : ℚ)) := by rfl
  have hs13 : baselineRationalSite (13 : Fin 16) = ((732757/2000000 : ℚ), (215311/250000 : ℚ)) := by rfl
  have hs14 : baselineRationalSite (14 : Fin 16) = ((313399/500000 : ℚ), (954497/1000000 : ℚ)) := by rfl
  have hs15 : baselineRationalSite (15 : Fin 16) = ((895009/1000000 : ℚ), (1734163/2000000 : ℚ)) := by rfl
  simp only [symbolicWallScaledSlab, symbolicWallSlab, baselineCellPolygon,
    hrange, List.map_cons, List.map_nil, List.append_nil]
  simp only [baselineBisector, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  norm_num [scaledWallFacet, SymbolicQuadratic.scaleByChart,
    SymbolicWallFacet.ofHalfplane, baselineRationalCap, baselineCenterBox,
    source, src0, src1, src2, src3, src4, src5, src6, src7, src8, src9, src10, src11, src12, src13, src14, src15, src16, src17, src18, src19, src20, src21, src22, src23]

def fw0 : SymbolicFarkasWitness := ⟨0, 9, ⟨1, 0, 1⟩, ⟨(78393024166152681205775180574419/547224550000000000000000000000000 : ℚ), (0 : ℚ), (78393024166152681205775180574419/547224550000000000000000000000000 : ℚ)⟩, ⟨(535503948579028101014310393/2188898200000000000000000000 : ℚ), (0 : ℚ), (535503948579028101014310393/2188898200000000000000000000 : ℚ)⟩⟩
def fw1 : SymbolicFarkasWitness := ⟨2, 8, ⟨1, 0, 1⟩, ⟨(734498531/18550500000 : ℚ), (499999/250000 : ℚ), (-734498531/18550500000 : ℚ)⟩, ⟨(999998/1521141 : ℚ), (0 : ℚ), (-999998/1521141 : ℚ)⟩⟩
def fw2 : SymbolicFarkasWitness := ⟨0, 2, ⟨1, 0, 1⟩, ⟨(1949048303832009912794092369/38200000000000000000000000000 : ℚ), (0 : ℚ), (1949048303832009912794092369/38200000000000000000000000000 : ℚ)⟩, ⟨(4844546603450490083386620347/19100000000000000000000000000 : ℚ), (0 : ℚ), (4844546603450490083386620347/19100000000000000000000000000 : ℚ)⟩⟩
def fw3 : SymbolicFarkasWitness := ⟨1, 2, ⟨1, 0, 1⟩, ⟨(1357358047574730191003623187/19100000000000000000000000000 : ℚ), (0 : ℚ), (1357358047574730191003623187/19100000000000000000000000000 : ℚ)⟩, ⟨(15801576414297555252696588657/38200000000000000000000000000 : ℚ), (0 : ℚ), (15801576414297555252696588657/38200000000000000000000000000 : ℚ)⟩⟩
def fw4 : SymbolicFarkasWitness := ⟨1, 2, ⟨1, 0, 1⟩, ⟨(0 : ℚ), (499999/250000 : ℚ), (0 : ℚ)⟩, ⟨(499999/500000 : ℚ), (0 : ℚ), (-499999/500000 : ℚ)⟩⟩
def fw5 : SymbolicFarkasWitness := ⟨1, 15, ⟨1, 0, 1⟩, ⟨(7752730948481741865919390148395999/17779960800000000000000000000000000 : ℚ), (0 : ℚ), (7752730948481741865919390148395999/17779960800000000000000000000000000 : ℚ)⟩, ⟨(1423580961542473870840584373/17779960800000000000000000000 : ℚ), (0 : ℚ), (1423580961542473870840584373/17779960800000000000000000000 : ℚ)⟩⟩
def fw6 : SymbolicFarkasWitness := ⟨1, 15, ⟨1, 0, 1⟩, ⟨(499999/500000 : ℚ), (-25316449367/116361000000 : ℚ), (-499999/500000 : ℚ)⟩, ⟨(0 : ℚ), (499999/116361 : ℚ), (0 : ℚ)⟩⟩
def fw7 : SymbolicFarkasWitness := ⟨0, 15, ⟨1, 0, 1⟩, ⟨(719973236201227257430124499953/79022048000000000000000000000000 : ℚ), (0 : ℚ), (719973236201227257430124499953/79022048000000000000000000000000 : ℚ)⟩, ⟨(821332325156910122972186417/1975551200000000000000000000 : ℚ), (0 : ℚ), (821332325156910122972186417/1975551200000000000000000000 : ℚ)⟩⟩
def fw8 : SymbolicFarkasWitness := ⟨0, 15, ⟨1, 0, 1⟩, ⟨(427507026617/33246000000000 : ℚ), (0 : ℚ), (427507026617/33246000000000 : ℚ)⟩, ⟨(8443249/33246000 : ℚ), (0 : ℚ), (8443249/33246000 : ℚ)⟩⟩
def fw9 : SymbolicFarkasWitness := ⟨0, 15, ⟨1, 0, 1⟩, ⟨(291819255346269125419566814316969/4444990200000000000000000000000000 : ℚ), (0 : ℚ), (291819255346269125419566814316969/4444990200000000000000000000000000 : ℚ)⟩, ⟨(1644916218263079491721204209/2222495100000000000000000000 : ℚ), (0 : ℚ), (1644916218263079491721204209/2222495100000000000000000000 : ℚ)⟩⟩
def fw10 : SymbolicFarkasWitness := ⟨1, 13, ⟨1, 0, 1⟩, ⟨(41200417599/17510750000 : ℚ), (-499999/250000 : ℚ), (-41200417599/17510750000 : ℚ)⟩, ⟨(499999/210129 : ℚ), (0 : ℚ), (-499999/210129 : ℚ)⟩⟩
def fw11 : SymbolicFarkasWitness := ⟨0, 8, ⟨1, 0, 1⟩, ⟨(705822230501306235053704618771/56115800000000000000000000000000 : ℚ), (0 : ℚ), (705822230501306235053704618771/56115800000000000000000000000000 : ℚ)⟩, ⟨(71326319097290710138554339/2300747800000000000000000000 : ℚ), (0 : ℚ), (71326319097290710138554339/2300747800000000000000000000 : ℚ)⟩⟩
def coverWitnesses : List SymbolicFarkasWitness := [fw0, fw1, fw2, fw3, fw4, fw5, fw6, fw7, fw8, fw9, fw10, fw11]

theorem fw0_checked : fw0.Check source f0 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw0, f0, src0, src9,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw1_checked : fw1.Check source f1 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw1, f1, src2, src8,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw2_checked : fw2.Check source f2 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw2, f2, src0, src2,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw3_checked : fw3.Check source f3 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw3, f3, src1, src2,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw4_checked : fw4.Check source f4 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw4, f4, src1, src2,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw5_checked : fw5.Check source f5 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw5, f5, src1, src15,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw6_checked : fw6.Check source f6 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw6, f6, src1, src15,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw7_checked : fw7.Check source f7 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw7, f7, src0, src15,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw8_checked : fw8.Check source f8 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw8, f8, src0, src15,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw9_checked : fw9.Check source f9 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw9, f9, src0, src15,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw10_checked : fw10.Check source f10 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw10, f10, src1, src13,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem fw11_checked : fw11.Check source f11 (15/32) (19/32) := by
  norm_num [SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    source, fw11, f11, src0, src8,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    SymbolicQuadratic.eval, quarticAdd, quarticSub,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem implication_checked :
    SymbolicPolygonImplicationCheck source facets coverWitnesses
      (15/32) (19/32) := by
  constructor
  · rfl
  · intro fw hfw
    change fw ∈ [(f0, fw0), (f1, fw1), (f2, fw2), (f3, fw3), (f4, fw4), (f5, fw5), (f6, fw6), (f7, fw7), (f8, fw8), (f9, fw9), (f10, fw10), (f11, fw11)] at hfw
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hfw
    rcases hfw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact fw0_checked | exact fw1_checked | exact fw2_checked | exact fw3_checked | exact fw4_checked | exact fw5_checked | exact fw6_checked | exact fw7_checked | exact fw8_checked | exact fw9_checked | exact fw10_checked | exact fw11_checked

theorem one_target_cover (t : ℝ) (hl : ((15/32 : ℚ) : ℝ) ≤ t)
    (hu : t ≤ ((19/32 : ℚ) : ℝ)) (p : Point)
    (hp : SymbolicPolygonContains (symbolicWallScaledSlab (3 : Fin 16)) t p) :
    SymbolicPolygonContains facets t p := by
  rw [source_matches] at hp
  exact symbolic_polygon_implication_sound source facets coverWitnesses
    (15/32) (19/32) implication_checked t hl hu p hp

#print axioms one_target_cover

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
