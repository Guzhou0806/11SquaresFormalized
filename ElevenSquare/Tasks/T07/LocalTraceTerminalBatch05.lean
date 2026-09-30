import ElevenSquare.Tasks.T07.LocalTraceCover
import Mathlib.Tactic.Linarith

/-! Generated exact polygon union certificates from far15y-self-300.json.
The emitter is untrusted; each closed split and arithmetic leaf is checked
inside Lean.  Triangle-to-semantic forbidden-center bridges are separate. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal step 7, row 230; interval ['243/256', '61/64']. -/
def terminal230Domain : Polygon :=
  [ { a := 25000000, b := 0, c := 13843539 },
    { a := 25000000, b := 25000000, c := 76450341 },
    { a := -10000000, b := 10000000, c := 20266053 },
    { a := -6250000, b := 0, c := -3223151 },
    { a := -5000000, b := -5000000, c := -14991547 },
    { a := 0, b := -100000000, c := -248092667 },
    { a := 100000000, b := -100000000, c := -193015209 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal230Triangle0Vertices : List QPoint :=
  [(3897086209678609993316174658072471223834801/9667039345693280214190977075383600000000000, 15578795200355255756598229020220301909555151/9667039345693280214190977075383600000000000), (25632062854051368811284673612761305077540849/9667039345693280214190977075383600000000000, 13074613653945756981712318247184686040078801/9667039345693280214190977075383600000000000), (4372524994978127449883570728760495337651151/9667039345693280214190977075383600000000000, 25072113196889620576645540799970827205685199/9667039345693280214190977075383600000000000)]
def terminal230Triangle0 : Polygon :=
  [ { a := -4034670256316611276236544473223862102049295937465779359675256225367896310000000000000, b := -35018812399812660267157300461288846471004543795507680145682444603855206668800000000000, c := -58060626866372005236874753822269438059337999809348250349979178754910175753249195784933 },
    { a := 1199749954294386359493322255278614116560639800000000, b := 2125953785907324136140110288400080973988969800000000, c := 6056465536222736369713694783892316768208723777284129 },
    { a := -4820836517225090523454469975768896716800000000000, b := 241434307658689673349419652457705410000000000000, c := -1554349717603334147825815738104842489480589344863 } ]
private theorem terminal230_leaf0 :
    Polygon.carrier (terminal230Domain) ⊆ terminal230Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal230Triangle0, l.contains p
  intro l hl
  simp only [terminal230Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 25000000, b := 0, c := 13843539 } : Halfplane).contains p :=
    hp _ (by simp [terminal230Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 76450341 } : Halfplane).contains p :=
    hp _ (by simp [terminal230Domain])
  have hs2 : ({ a := -10000000, b := 10000000, c := 20266053 } : Halfplane).contains p :=
    hp _ (by simp [terminal230Domain])
  have hs3 : ({ a := -6250000, b := 0, c := -3223151 } : Halfplane).contains p :=
    hp _ (by simp [terminal230Domain])
  have hs4 : ({ a := -5000000, b := -5000000, c := -14991547 } : Halfplane).contains p :=
    hp _ (by simp [terminal230Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -248092667 } : Halfplane).contains p :=
    hp _ (by simp [terminal230Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193015209 } : Halfplane).contains p :=
    hp _ (by simp [terminal230Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs5 ⊢
    linarith only [hs2, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal230_cover_cert :
    PolygonCoverCert [terminal230Triangle0] terminal230Domain :=
  PolygonCoverCert.leaf _ terminal230Triangle0 (by simp) terminal230_leaf0
theorem terminal230_polygon_cover :
    terminal230Domain.carrier ⊆ ⋃ K ∈ [terminal230Triangle0], Polygon.carrier K :=
  terminal230_cover_cert.sound

/-- Archived far15 terminal step 7, row 231; interval ['61/64', '245/256']. -/
def terminal231Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55402419 },
    { a := 12500000, b := 12500000, c := 38248293 },
    { a := -50000000, b := 50000000, c := 101614573 },
    { a := -50000000, b := 0, c := -25689299 },
    { a := -100000000, b := -100000000, c := -299447389 },
    { a := 0, b := -100000000, c := -247915459 },
    { a := 50000000, b := -50000000, c := -96512877 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal231Triangle0Vertices : List QPoint :=
  [(1233183723400646149718238158733416122210293/3044590563518158905981620155798000000000000, 4900045807666241488607481725339989285939851/3044590563518158905981620155798000000000000), (8079128586904769543499285646764425246340149/3044590563518158905981620155798000000000000, 4123604715189917704364296758562040078630293/3044590563518158905981620155798000000000000), (1370681407724506597358144253618308823219851/3044590563518158905981620155798000000000000, 7890535338031206311150852195230170041389707/3044590563518158905981620155798000000000000)]
def terminal231Triangle0 : Polygon :=
  [ { a := -47278904465622911229519098870981918557624452210291890485282578487490345680000000000, b := -416861982595805289943541971490359453137251435949073979589023775358066101760000000000, c := -690058758906976760949665665484692096433466181652457307574972913443343345989247083439 },
    { a := 75338612456825772135731108733362599255188280000000, b := 134168943583605258922822827862922328462405960000000, c := 381637531139301729164034537026071912370644912734881 },
    { a := -60981444016553152717824502013346693120000000000, b := 2803824341755142899696593633877494160000000000, c := -20187429211633842905324066035561331281636003443 } ]
private theorem terminal231_leaf0 :
    Polygon.carrier (terminal231Domain) ⊆ terminal231Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal231Triangle0, l.contains p
  intro l hl
  simp only [terminal231Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 55402419 } : Halfplane).contains p :=
    hp _ (by simp [terminal231Domain])
  have hs1 : ({ a := 12500000, b := 12500000, c := 38248293 } : Halfplane).contains p :=
    hp _ (by simp [terminal231Domain])
  have hs2 : ({ a := -50000000, b := 50000000, c := 101614573 } : Halfplane).contains p :=
    hp _ (by simp [terminal231Domain])
  have hs3 : ({ a := -50000000, b := 0, c := -25689299 } : Halfplane).contains p :=
    hp _ (by simp [terminal231Domain])
  have hs4 : ({ a := -100000000, b := -100000000, c := -299447389 } : Halfplane).contains p :=
    hp _ (by simp [terminal231Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -247915459 } : Halfplane).contains p :=
    hp _ (by simp [terminal231Domain])
  have hs6 : ({ a := 50000000, b := -50000000, c := -96512877 } : Halfplane).contains p :=
    hp _ (by simp [terminal231Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
theorem terminal231_cover_cert :
    PolygonCoverCert [terminal231Triangle0] terminal231Domain :=
  PolygonCoverCert.leaf _ terminal231Triangle0 (by simp) terminal231_leaf0
theorem terminal231_polygon_cover :
    terminal231Domain.carrier ⊆ ⋃ K ∈ [terminal231Triangle0], Polygon.carrier K :=
  terminal231_cover_cert.sound

/-- Archived far15 terminal step 7, row 232; interval ['245/256', '123/128']. -/
def terminal232Domain : Polygon :=
  [ { a := 12500000, b := 0, c := 6929007 },
    { a := 25000000, b := 25000000, c := 76543289 },
    { a := -4000000, b := 0, c := -2047467 },
    { a := -100000000, b := -100000000, c := -299063843 },
    { a := 0, b := -10000000, c := -24773819 },
    { a := 100000000, b := -100000000, c := -193034593 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal232Triangle0Vertices : List QPoint :=
  [(1175246139711909072037562947536871934513181/2887925673775870488493509176902000000000000, 4641856279597379348107997374905115912451683/2887925673775870488493509176902000000000000), (7669451325318427940091641675393778577268317/2887925673775870488493509176902000000000000, 3916935314680399313672423716611158211093181/2887925673775870488493509176902000000000000), (1294101680067788440397485056974198647171683/2887925673775870488493509176902000000000000, 7478995528626029224264056714568833041886819/2887925673775870488493509176902000000000000)]
def terminal232Triangle0 : Polygon :=
  [ { a := -1674814292833698990595392447830894080726104547263255424357131399391776643200000000, b := -15003825509025166451956706989168671920934764154799973030822649063114454937600000000, c := -24797702149933117714968890528194115586623878780533676102832994153846805743733860407 },
    { a := 356206021394562991059163299795767483079363800000000, b := 637534964525063949969415661841957993009663400000000, c := 1810672624730611116185942548350755218893575156881101 },
    { a := -464640903028392725659750565759838453760000000, b := 19465081109357171231724410813787784320000000, c := -157799531613360924693163296098160691922657727 } ]
private theorem terminal232_leaf0 :
    Polygon.carrier (terminal232Domain) ⊆ terminal232Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal232Triangle0, l.contains p
  intro l hl
  simp only [terminal232Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 12500000, b := 0, c := 6929007 } : Halfplane).contains p :=
    hp _ (by simp [terminal232Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 76543289 } : Halfplane).contains p :=
    hp _ (by simp [terminal232Domain])
  have hs2 : ({ a := -4000000, b := 0, c := -2047467 } : Halfplane).contains p :=
    hp _ (by simp [terminal232Domain])
  have hs3 : ({ a := -100000000, b := -100000000, c := -299063843 } : Halfplane).contains p :=
    hp _ (by simp [terminal232Domain])
  have hs4 : ({ a := 0, b := -10000000, c := -24773819 } : Halfplane).contains p :=
    hp _ (by simp [terminal232Domain])
  have hs5 : ({ a := 100000000, b := -100000000, c := -193034593 } : Halfplane).contains p :=
    hp _ (by simp [terminal232Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs3 hs5 ⊢
    linarith only [hs3, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal232_cover_cert :
    PolygonCoverCert [terminal232Triangle0] terminal232Domain :=
  PolygonCoverCert.leaf _ terminal232Triangle0 (by simp) terminal232_leaf0
theorem terminal232_polygon_cover :
    terminal232Domain.carrier ⊆ ⋃ K ∈ [terminal232Triangle0], Polygon.carrier K :=
  terminal232_cover_cert.sound

/-- Archived far15 terminal step 7, row 233; interval ['123/128', '247/256']. -/
def terminal233Domain : Polygon :=
  [ { a := 12500000, b := 0, c := 6932881 },
    { a := 100000000, b := 100000000, c := 306361771 },
    { a := 0, b := 50000000, c := 127683557 },
    { a := -3125000, b := 0, c := -1593583 },
    { a := -100000000, b := -100000000, c := -298680299 },
    { a := 0, b := -100000000, c := -247560869 },
    { a := 100000000, b := -100000000, c := -193041747 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 5, 11).
def terminal233Triangle0Vertices : List QPoint :=
  [(5057546617641615117631747057362985118470781/12369769315338843683053616983942000000000000, 19856617920637866064310026952897071261406211/12369769315338843683053616983942000000000000), (256057098246348872294460995102055123/95638262354043239251152027343750000, 90563012907659564326985361279913783897/48966790325270138496589838000000000000), (5517276539181148517805923703989020530526211/12369769315338843683053616983942000000000000, 32010918824049530137456397461905435185929219/12369769315338843683053616983942000000000000)]
def terminal233Triangle0 : Polygon :=
  [ { a := 147928731880926997381333765812062020220869217125227204166065934498156000000000000, b := -1374040200487207488326615590789166591185324254846741590445124050927914000000000000, c := -2145200458846863082414095333618229010222847830085122911823947079355812624540490379 },
    { a := 447228372006673379020908158675157583373281824019354174092962835494548000000000000, b := 1351528701812928264372110310719592042958131220073478838840914820207574000000000000, c := 3697009782545211469704978946498041295397378222990606859932602414794115811393311477 },
    { a := -6244655383001139134203323569237407744000000000000, b := 236200745076395220127908816308372490000000000000, c := -2174049254882671790566270165797100927591289714747 } ]
private theorem terminal233_leaf0 :
    Polygon.carrier (terminal233Domain) ⊆ terminal233Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal233Triangle0, l.contains p
  intro l hl
  simp only [terminal233Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 12500000, b := 0, c := 6932881 } : Halfplane).contains p :=
    hp _ (by simp [terminal233Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 306361771 } : Halfplane).contains p :=
    hp _ (by simp [terminal233Domain])
  have hs2 : ({ a := 0, b := 50000000, c := 127683557 } : Halfplane).contains p :=
    hp _ (by simp [terminal233Domain])
  have hs3 : ({ a := -3125000, b := 0, c := -1593583 } : Halfplane).contains p :=
    hp _ (by simp [terminal233Domain])
  have hs4 : ({ a := -100000000, b := -100000000, c := -298680299 } : Halfplane).contains p :=
    hp _ (by simp [terminal233Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -247560869 } : Halfplane).contains p :=
    hp _ (by simp [terminal233Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193041747 } : Halfplane).contains p :=
    hp _ (by simp [terminal233Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs6 ⊢
    linarith only [hs4, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal233_cover_cert :
    PolygonCoverCert [terminal233Triangle0] terminal233Domain :=
  PolygonCoverCert.leaf _ terminal233Triangle0 (by simp) terminal233_leaf0
theorem terminal233_polygon_cover :
    terminal233Domain.carrier ⊆ ⋃ K ∈ [terminal233Triangle0], Polygon.carrier K :=
  terminal233_cover_cert.sound

/-- Archived far15 terminal step 7, row 234; interval ['247/256', '31/32']. -/
def terminal234Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 27747689 },
    { a := 50000000, b := 50000000, c := 153276079 },
    { a := 0, b := 20000000, c := 51149921 },
    { a := -12500000, b := 0, c := -6350319 },
    { a := -25000000, b := -25000000, c := -74574189 },
    { a := 0, b := -100000000, c := -247383509 },
    { a := 50000000, b := -50000000, c := -96523617 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 5, 11).
def terminal234Triangle0Vertices : List QPoint :=
  [(4096793397192438116152593854424307945586121/9973297946283696588565354499514800000000000, 15989100403629559671154739222102870596148919/9973297946283696588565354499514800000000000), (7616755023540270354399769771860153/2844810084179239902601212500000000, 168546591537503583942456351528489971/91033922693735676883238800000000000), (4427807682236102155405838035930446391476919/9973297946283696588565354499514800000000000, 25790170606499612140147344556633594087773879/9973297946283696588565354499514800000000000)]
def terminal234Triangle0 : Polygon :=
  [ { a := 225414845147710325470181061692188166103189703992968588515996327213600000000000, b := -2057906178063623465570220533432142487242170893320204501587075711766000000000000, c := -3206621382949391266822044717262301876596001910914050485715473743274988898694933 },
    { a := 133363004403247655699239533067804284447781621335237631086320678646880000000000, b := 405554529845687273546769628534579035270866165556068483059034871040720000000000, c := 1107941055195212112983337667971113416911549244704693452468359821340901001902447 },
    { a := -5055265263012280126812006888714061824000000000000, b := 170732887542430601899650303677193861200000000000, c := -1802865227359168600304928792187414169723219668119 } ]
private theorem terminal234_leaf0 :
    Polygon.carrier (terminal234Domain) ⊆ terminal234Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal234Triangle0, l.contains p
  intro l hl
  simp only [terminal234Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 27747689 } : Halfplane).contains p :=
    hp _ (by simp [terminal234Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 153276079 } : Halfplane).contains p :=
    hp _ (by simp [terminal234Domain])
  have hs2 : ({ a := 0, b := 20000000, c := 51149921 } : Halfplane).contains p :=
    hp _ (by simp [terminal234Domain])
  have hs3 : ({ a := -12500000, b := 0, c := -6350319 } : Halfplane).contains p :=
    hp _ (by simp [terminal234Domain])
  have hs4 : ({ a := -25000000, b := -25000000, c := -74574189 } : Halfplane).contains p :=
    hp _ (by simp [terminal234Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -247383509 } : Halfplane).contains p :=
    hp _ (by simp [terminal234Domain])
  have hs6 : ({ a := 50000000, b := -50000000, c := -96523617 } : Halfplane).contains p :=
    hp _ (by simp [terminal234Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal234_cover_cert :
    PolygonCoverCert [terminal234Triangle0] terminal234Domain :=
  PolygonCoverCert.leaf _ terminal234Triangle0 (by simp) terminal234_leaf0
theorem terminal234_polygon_cover :
    terminal234Domain.carrier ⊆ ⋃ K ∈ [terminal234Triangle0], Polygon.carrier K :=
  terminal234_cover_cert.sound

/-- Archived far15 terminal step 7, row 235; interval ['31/32', '249/256']. -/
def terminal235Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55529029 },
    { a := 3125000, b := 3125000, c := 9585759 },
    { a := -5000000, b := 5000000, c := 10276177 },
    { a := -100000000, b := 0, c := -50610373 },
    { a := -100000000, b := -100000000, c := -297913211 },
    { a := 0, b := -100000000, c := -247206121 },
    { a := 50000000, b := -50000000, c := -96525537 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 5, 11).
def terminal235Triangle0Vertices : List QPoint :=
  [(64814209848475776356414017934517465970041/157053100726407309463471925364400000000000, 251464600578924368997561135138940581990151/157053100726407309463471925364400000000000), (147472671482665901280480639599698599/55078818750761603906410187500000000, 22867284126391838091828150977881326763/12337655400170599275035882000000000000), (69404776428471117191399299308287123174151/157053100726407309463471925364400000000000, 405826534402767700379615266555514358109959/157053100726407309463471925364400000000000)]
def terminal235Triangle0 : Polygon :=
  [ { a := 488894289957283278098446111900613290594534090659926636038088649255200000000000, b := -4388417647497290974872552247422384404922170342268401115701554751372400000000000, c := -6824726088443114820002519857995851548369283803553234455346586136120493886145293 },
    { a := 1415570056465234082084827970620218137095479203036814422135842301400800000000000, b := 4331780818941768778714404428400925998903856649172127819841506876352400000000000, c := 11818925651553358665356554367903978610663181088452110680777403025009821069323571 },
    { a := -79928720446489019190625840031853363200000000000, b := 2376998679494174628729647590390194000000000000, c := -29179849460003059584738985539050239212780090663 } ]
private theorem terminal235_leaf0 :
    Polygon.carrier (terminal235Domain) ⊆ terminal235Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal235Triangle0, l.contains p
  intro l hl
  simp only [terminal235Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 55529029 } : Halfplane).contains p :=
    hp _ (by simp [terminal235Domain])
  have hs1 : ({ a := 3125000, b := 3125000, c := 9585759 } : Halfplane).contains p :=
    hp _ (by simp [terminal235Domain])
  have hs2 : ({ a := -5000000, b := 5000000, c := 10276177 } : Halfplane).contains p :=
    hp _ (by simp [terminal235Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -50610373 } : Halfplane).contains p :=
    hp _ (by simp [terminal235Domain])
  have hs4 : ({ a := -100000000, b := -100000000, c := -297913211 } : Halfplane).contains p :=
    hp _ (by simp [terminal235Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -247206121 } : Halfplane).contains p :=
    hp _ (by simp [terminal235Domain])
  have hs6 : ({ a := 50000000, b := -50000000, c := -96525537 } : Halfplane).contains p :=
    hp _ (by simp [terminal235Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal235_cover_cert :
    PolygonCoverCert [terminal235Triangle0] terminal235Domain :=
  PolygonCoverCert.leaf _ terminal235Triangle0 (by simp) terminal235_leaf0
theorem terminal235_polygon_cover :
    terminal235Domain.carrier ⊆ ⋃ K ∈ [terminal235Triangle0], Polygon.carrier K :=
  terminal235_cover_cert.sound

/-- Archived far15 terminal step 7, row 236; interval ['249/256', '125/128']. -/
def terminal236Domain : Polygon :=
  [ { a := 20000000, b := 0, c := 11112797 },
    { a := 25000000, b := 25000000, c := 76734533 },
    { a := -6250000, b := 6250000, c := 12881367 },
    { a := -100000000, b := 0, c := -50418129 },
    { a := -20000000, b := -20000000, c := -59505933 },
    { a := 0, b := -50000000, c := -123514357 },
    { a := 20000000, b := -20000000, c := -38610657 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 6, 11).
def terminal236Triangle0Vertices : List QPoint :=
  [(20999948302502008340201578267632496533335093/50650603206962164009189677421078000000000000, 11570858103885466948471694853078461121384093/7235800458137452001312811060154000000000000), (136209557026209482729689452102670695737824907/50650603206962164009189677421078000000000000, 16982051815394860451906217658635781671075907/7235800458137452001312811060154000000000000), (3182939922689244081732571924483422126824093/7235800458137452001312811060154000000000000, 130784623156715736014241911518692588126264907/50650603206962164009189677421078000000000000)]
def terminal236Triangle0 : Polygon :=
  [ { a := 757567119611315090480833192778024876956853960000000, b := -2304192174474149487789757476700763984089796280000000, c := -3370571793969995065463320944171202151237469317718683 },
    { a := 4021745840609521668059746092905343011553185197294433430018272124393567570160000000000, b := 38470476243603331231997890771905935246741377962989914487051097920862001093120000000000, c := 101103506013923361612184975953073317830909017249202997194219526288434575065640283551323 },
    { a := -1035249704971227948670388184396510085120000000000, b := 26628035117964148862911197213809126160000000000, c := -386637562696147974756659890348148441879558981627 } ]
private theorem terminal236_leaf0 :
    Polygon.carrier (terminal236Domain) ⊆ terminal236Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal236Triangle0, l.contains p
  intro l hl
  simp only [terminal236Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 20000000, b := 0, c := 11112797 } : Halfplane).contains p :=
    hp _ (by simp [terminal236Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 76734533 } : Halfplane).contains p :=
    hp _ (by simp [terminal236Domain])
  have hs2 : ({ a := -6250000, b := 6250000, c := 12881367 } : Halfplane).contains p :=
    hp _ (by simp [terminal236Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -50418129 } : Halfplane).contains p :=
    hp _ (by simp [terminal236Domain])
  have hs4 : ({ a := -20000000, b := -20000000, c := -59505933 } : Halfplane).contains p :=
    hp _ (by simp [terminal236Domain])
  have hs5 : ({ a := 0, b := -50000000, c := -123514357 } : Halfplane).contains p :=
    hp _ (by simp [terminal236Domain])
  have hs6 : ({ a := 20000000, b := -20000000, c := -38610657 } : Halfplane).contains p :=
    hp _ (by simp [terminal236Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs6 ⊢
    linarith only [hs4, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal236_cover_cert :
    PolygonCoverCert [terminal236Triangle0] terminal236Domain :=
  PolygonCoverCert.leaf _ terminal236Triangle0 (by simp) terminal236_leaf0
theorem terminal236_polygon_cover :
    terminal236Domain.carrier ⊆ ⋃ K ∈ [terminal236Triangle0], Polygon.carrier K :=
  terminal236_cover_cert.sound

/-- Archived far15 terminal step 7, row 237; interval ['125/128', '251/256']. -/
def terminal237Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55600227 },
    { a := 5000000, b := 5000000, c := 15356683 },
    { a := 0, b := 100000000, c := 256907829 },
    { a := -10000000, b := 0, c := -5022583 },
    { a := -100000000, b := -100000000, c := -297146117 },
    { a := 0, b := -100000000, c := -246851299 },
    { a := 100000000, b := -100000000, c := -193053887 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 6, 11).
def terminal237Triangle0Vertices : List QPoint :=
  [(5315547969819903760029088907447277339789693/12761835292976295958605816810886000000000000, 20381882576327368398421516208431337992740099/12761835292976295958605816810886000000000000), (34294677505629567019964632020910820513130307/12761835292976295958605816810886000000000000, 29977097834091614078527552296092113944399901/12761835292976295958605816810886000000000000), (5588048653087627187273233313926066561700099/12761835292976295958605816810886000000000000, 32927820881338634981792236839264539265410307/12761835292976295958605816810886000000000000)]
def terminal237Triangle0 : Polygon :=
  [ { a := 959521525776424568010603608766077595165980200000000, b := -2897912953580966325993554311346354317334061400000000, c := -4228587628588676225614183592209195641851997354794271 },
    { a := 753132830483111875822745527639891714640586680478028006938549339482801594320000000000, b := 7326985384654827148018309991810240004925986391011495680027561990983272885760000000000, c := 19234710338267439183354842988289576616200797644594557374889852249814389517742288491681 },
    { a := -261885111573754850314711622543519170560000000000, b := 5688205226785394634669784668948107920000000000, c := -99995534564834817620862094101747264428606581539 } ]
private theorem terminal237_leaf0 :
    Polygon.carrier (terminal237Domain) ⊆ terminal237Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal237Triangle0, l.contains p
  intro l hl
  simp only [terminal237Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 55600227 } : Halfplane).contains p :=
    hp _ (by simp [terminal237Domain])
  have hs1 : ({ a := 5000000, b := 5000000, c := 15356683 } : Halfplane).contains p :=
    hp _ (by simp [terminal237Domain])
  have hs2 : ({ a := 0, b := 100000000, c := 256907829 } : Halfplane).contains p :=
    hp _ (by simp [terminal237Domain])
  have hs3 : ({ a := -10000000, b := 0, c := -5022583 } : Halfplane).contains p :=
    hp _ (by simp [terminal237Domain])
  have hs4 : ({ a := -100000000, b := -100000000, c := -297146117 } : Halfplane).contains p :=
    hp _ (by simp [terminal237Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -246851299 } : Halfplane).contains p :=
    hp _ (by simp [terminal237Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193053887 } : Halfplane).contains p :=
    hp _ (by simp [terminal237Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal237_cover_cert :
    PolygonCoverCert [terminal237Triangle0] terminal237Domain :=
  PolygonCoverCert.leaf _ terminal237Triangle0 (by simp) terminal237_leaf0
theorem terminal237_polygon_cover :
    terminal237Domain.carrier ⊆ ⋃ K ∈ [terminal237Triangle0], Polygon.carrier K :=
  terminal237_cover_cert.sound

/-- Archived far15 terminal step 7, row 238; interval ['251/256', '63/64']. -/
def terminal238Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55637741 },
    { a := 25000000, b := 25000000, c := 76832711 },
    { a := -100000000, b := 100000000, c := 207263873 },
    { a := -20000000, b := 0, c := -10006697 },
    { a := -50000000, b := -50000000, c := -148381283 },
    { a := 0, b := -3125000, c := -7708559 },
    { a := 100000000, b := -100000000, c := -193052897 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 7, 11).
def terminal238Triangle0Vertices : List QPoint :=
  [(21527299427255983705802994731920714400804229/51447224718670629381410328620918000000000000, 82063267698935134845978944156760863868300539/51447224718670629381410328620918000000000000), (121620918702210691357494948048047790452035771/51447224718670629381410328620918000000000000, 148611325158450944763163973685637675711599461/51447224718670629381410328620918000000000000), (22424377145435073222740133268895498848780539/51447224718670629381410328620918000000000000, 132644506282179797754336450507792738546795771/51447224718670629381410328620918000000000000)]
def terminal238Triangle0 : Polygon :=
  [ { a := 6654805745951580991718502952887681184329892200000000, b := -10009361927495470765169195331612707605123154200000000, c := -13181293162780923514228249489561243777626715002040837 },
    { a := -410724259384916877964423796155289897453566390634056203764649076502948793710000000000000, b := 2551693382393192448492175675508972649933724954335118607185917251273064071488000000000000, c := 6399915155701938413798337246391958433786216776072539478548652905000485531886579431917481 },
    { a := -26499024930295118416741780783433476096000000000000, b := 469970397805056199399183351952085930000000000000, c := -10338461220165821582497342447687855716414110415723 } ]
private theorem terminal238_leaf0 :
    Polygon.carrier (terminal238Domain) ⊆ terminal238Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal238Triangle0, l.contains p
  intro l hl
  simp only [terminal238Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 55637741 } : Halfplane).contains p :=
    hp _ (by simp [terminal238Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 76832711 } : Halfplane).contains p :=
    hp _ (by simp [terminal238Domain])
  have hs2 : ({ a := -100000000, b := 100000000, c := 207263873 } : Halfplane).contains p :=
    hp _ (by simp [terminal238Domain])
  have hs3 : ({ a := -20000000, b := 0, c := -10006697 } : Halfplane).contains p :=
    hp _ (by simp [terminal238Domain])
  have hs4 : ({ a := -50000000, b := -50000000, c := -148381283 } : Halfplane).contains p :=
    hp _ (by simp [terminal238Domain])
  have hs5 : ({ a := 0, b := -3125000, c := -7708559 } : Halfplane).contains p :=
    hp _ (by simp [terminal238Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193052897 } : Halfplane).contains p :=
    hp _ (by simp [terminal238Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs6 ⊢
    linarith only [hs4, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
theorem terminal238_cover_cert :
    PolygonCoverCert [terminal238Triangle0] terminal238Domain :=
  PolygonCoverCert.leaf _ terminal238Triangle0 (by simp) terminal238_leaf0
theorem terminal238_polygon_cover :
    terminal238Domain.carrier ⊆ ⋃ K ∈ [terminal238Triangle0], Polygon.carrier K :=
  terminal238_cover_cert.sound

/-- Archived far15 terminal step 7, row 239; interval ['63/64', '125613/127232']. -/
def terminal239Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55626251 },
    { a := 100000000, b := 100000000, c := 307426993 },
    { a := -20000000, b := 20000000, c := 41529137 },
    { a := -100000000, b := 0, c := -49890653 },
    { a := -100000000, b := -100000000, c := -296477881 },
    { a := 0, b := -100000000, c := -246542911 },
    { a := 5000000, b := -5000000, c := -9655083 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 7, 11).
def terminal239Triangle0Vertices : List QPoint :=
  [(67147308888642398749453733174218545871434730729/159931731872949678357578302565033082800000000000, 254790275915165939653720100859784087805680996247/159931731872949678357578302565033082800000000000), (377851280737203340624543923954956299350175133271/159931731872949678357578302565033082800000000000, 462297717392679475191456300747903219226409543753/159931731872949678357578302565033082800000000000), (69393471610169323021540601797022535808760804247/159931731872949678357578302565033082800000000000, 412119824137908531075280122481471476295776229271/159931731872949678357578302565033082800000000000)]
def terminal239Triangle0 : Polygon :=
  [ { a := 20750744147751353553773619988811913142072854750600000000, b := -31070397184856094187509019078073775347874040254200000000, c := -40786642951800126284564879740426402890716320479147297641 },
    { a := -53500249133143445856116765449449430395647386872255134299835257579856118680975634064000000000, b := 328881277489481963969736124490872514751491157880700022554894397432552140323494901248000000000, c := 824263732269098413679278790925171505431818144953155802385283406120307603774582512569957743043 },
    { a := -816727541671481799453993740801580339766227812352000000000, b := 11660256947725891661332347213107502093516749264000000000, c := -324326735076748561702430044778436025363024427579030065183 } ]
private theorem terminal239_leaf0 :
    Polygon.carrier (terminal239Domain) ⊆ terminal239Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal239Triangle0, l.contains p
  intro l hl
  simp only [terminal239Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 55626251 } : Halfplane).contains p :=
    hp _ (by simp [terminal239Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 307426993 } : Halfplane).contains p :=
    hp _ (by simp [terminal239Domain])
  have hs2 : ({ a := -20000000, b := 20000000, c := 41529137 } : Halfplane).contains p :=
    hp _ (by simp [terminal239Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -49890653 } : Halfplane).contains p :=
    hp _ (by simp [terminal239Domain])
  have hs4 : ({ a := -100000000, b := -100000000, c := -296477881 } : Halfplane).contains p :=
    hp _ (by simp [terminal239Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -246542911 } : Halfplane).contains p :=
    hp _ (by simp [terminal239Domain])
  have hs6 : ({ a := 5000000, b := -5000000, c := -9655083 } : Halfplane).contains p :=
    hp _ (by simp [terminal239Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal239_cover_cert :
    PolygonCoverCert [terminal239Triangle0] terminal239Domain :=
  PolygonCoverCert.leaf _ terminal239Triangle0 (by simp) terminal239_leaf0
theorem terminal239_polygon_cover :
    terminal239Domain.carrier ⊆ ⋃ K ∈ [terminal239Triangle0], Polygon.carrier K :=
  terminal239_cover_cert.sound

end
end ElevenSquare.Tasks.T07
