import ElevenSquare.Tasks.T07.LocalTraceCover
import Mathlib.Tactic.Linarith

/-! Generated exact polygon union certificates from far15y-self-300.json.
The emitter is untrusted; each closed split and arithmetic leaf is checked
inside Lean.  Triangle-to-semantic forbidden-center bridges are separate. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal step 7, row 20; interval ['1/64', '5/256']. -/
def terminal20Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 56445771 },
    { a := 41627165226232534359131560014100000000, b := 1463907360920690966117904691200000000, c := 27280446129256002902558328993678929159 },
    { a := 100000000, b := 100000000, c := 315052403 },
    { a := -20000000, b := 20000000, c := 42698919 },
    { a := -100000000, b := 0, c := -50778903 },
    { a := -4000000, b := -4000000, c := -11895749 },
    { a := 0, b := -100000000, c := -246614821 },
    { a := 20000000, b := -20000000, c := -38537893 } ]
def terminal20Cut : Halfplane := { a := -79795570528827996436741756580507564000000000000, b := 124045513370688872228672244808896326000000000000, c := 283655761491711105572528389809811173943137472953 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal20Triangle0Vertices : List QPoint :=
  [(4351616787207992776139726870163308793507/10586137138791430701228797242000000000000, 3858098352758377690593397604438451629307/1512305305541632957318399606000000000000), (200698391665737986283581193238113187/470677947828769641125434000000000000, 3788677131539492909261286255572363/1838585733706131410646226562500000), (13034802723156213832146784006786051613507/10586137138791430701228797242000000000000, 4656054058046657654960815170243527269307/1512305305541632957318399606000000000000)]
def terminal20Triangle0 : Polygon :=
  [ { a := -2443944049980605325672264266188155775029374301586556216031811090000000000000, b := -76410638568095662711400786142280264098881161872699437277673216000000000000, c := -1199559962236795912847194847083129087582589209861157155021085872495086557367 },
    { a := 5073005126744028167740411585736101506052555345215429900826131090000000000000, b := -4010573498379647414193395788300349636452217102369165305606206784000000000000, c := -6101234775074889784696066420864745197006977221745892301426056982052677642633 },
    { a := -79795570528827996436741756580507564000000000000, b := 124045513370688872228672244808896326000000000000, c := 283655761491711105572528389809811173943137472953 } ]
private theorem terminal20_leaf0 :
    Polygon.carrier (terminal20Cut :: terminal20Domain) ⊆ terminal20Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal20Triangle0, l.contains p
  intro l hl
  simp only [terminal20Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal20Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 56445771 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs2 : ({ a := 41627165226232534359131560014100000000, b := 1463907360920690966117904691200000000, c := 27280446129256002902558328993678929159 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs3 : ({ a := 100000000, b := 100000000, c := 315052403 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs4 : ({ a := -20000000, b := 20000000, c := 42698919 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -50778903 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs6 : ({ a := -4000000, b := -4000000, c := -11895749 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246614821 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs8 : ({ a := 20000000, b := -20000000, c := -38537893 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  simp only [Halfplane.contains, terminal20Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs7 ⊢
    linarith only [hs1, hs7]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal20Triangle1Vertices : List QPoint :=
  [(3211390095948308274340179831929889153507/10586137138791430701228797242000000000000, 5659958085885669671648209408857009169307/1512305305541632957318399606000000000000), (510934706885871745977677744851969050693/1512305305541632957318399606000000000000, 29236345932805162933240309541583654453507/10586137138791430701228797242000000000000), (1249033746257140263302672383851466190693/1512305305541632957318399606000000000000, 21283419895815563952209680107314735353507/10586137138791430701228797242000000000000)]
def terminal20Triangle1 : Polygon :=
  [ { a := -4438775771204957926169795666608393600000000, b := -156098943793762920548039352611635200000000, c := -1930754782001852533049247732286761466825341 },
    { a := -56806614549925707007361638816206565000000000000, b := -36904951968563425866249731949974857000000000000, c := -121114739234576898772058563399260972117581266617 },
    { a := 155288356543515549778816883738308418187432043884940481646674217545091200000000, b := 46848705392104136465563853768599831807525523057087413184850812042598400000000, c := 222444072056484074770077258453652117867163310615127564985795379392055220011623 } ]
private theorem terminal20_leaf1 :
    Polygon.carrier ((⟨-terminal20Cut.a, -terminal20Cut.b, -terminal20Cut.c⟩ : Halfplane) :: terminal20Domain) ⊆ terminal20Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal20Triangle1, l.contains p
  intro l hl
  simp only [terminal20Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal20Cut.a, -terminal20Cut.b, -terminal20Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 56445771 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs2 : ({ a := 41627165226232534359131560014100000000, b := 1463907360920690966117904691200000000, c := 27280446129256002902558328993678929159 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs3 : ({ a := 100000000, b := 100000000, c := 315052403 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs4 : ({ a := -20000000, b := 20000000, c := 42698919 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -50778903 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs6 : ({ a := -4000000, b := -4000000, c := -11895749 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246614821 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  have hs8 : ({ a := 20000000, b := -20000000, c := -38537893 } : Halfplane).contains p :=
    hp _ (by simp [terminal20Domain])
  simp only [Halfplane.contains, terminal20Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal20_cover_cert :
    PolygonCoverCert [terminal20Triangle0, terminal20Triangle1] terminal20Domain := by
  refine PolygonCoverCert.split terminal20Domain terminal20Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal20Triangle0 (by simp) terminal20_leaf0
  · exact PolygonCoverCert.leaf _ terminal20Triangle1 (by simp) terminal20_leaf1
theorem terminal20_polygon_cover :
    terminal20Domain.carrier ⊆ ⋃ K ∈ [terminal20Triangle0, terminal20Triangle1], Polygon.carrier K :=
  terminal20_cover_cert.sound

/-- Archived far15 terminal step 7, row 21; interval ['5/256', '3/128']. -/
def terminal21Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28280499 },
    { a := 12500000, b := 12500000, c := 38828349 },
    { a := -100000000, b := 0, c := -51149897 },
    { a := 0, b := -100000000, c := -246852147 },
    { a := 100000000, b := -100000000, c := -192640313 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal21Triangle0Vertices : List QPoint :=
  [(5452778460969318715994047370363766493383117/13384748373344073758908453262054000000000000, 34093074861428367727037287115048227286602931/13384748373344073758908453262054000000000000), (10843185154670994166507889561912823443/25420486266343583434950746000000000000, 816952153790905964621065703132116957/397195097911618491171105406250000000), (16431500662266593522330365353259386538723117/13384748373344073758908453262054000000000000, 41155429459551479092690835676637728231362931/13384748373344073758908453262054000000000000)]
def terminal21Triangle0 : Polygon :=
  [ { a := -166841804552986454520967574567727841283225406981041003013910569057134000000000000, b := -6521024880366530174218236526939181850344889318744689091764910576640000000000000, c := -84579340313179968889802382603478808783440102635578121118095791663269026843553417 },
    { a := 346370292622623464420415443834300636686817341560884859784977360017134000000000000, b := -272563432059712238508773677685065046348279137357398542981421913063360000000000000, c := -412864049037627149764245633135098368298932050627970912400312826835788858292086583 },
    { a := -706235459812311136565354856158950094476000000000000, b := 1097872220129727480633631798289562004534000000000000, c := 2508743037142252106496460591541393089964253989585953 } ]
private theorem terminal21_leaf0 :
    Polygon.carrier (terminal21Domain) ⊆ terminal21Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal21Triangle0, l.contains p
  intro l hl
  simp only [terminal21Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 28280499 } : Halfplane).contains p :=
    hp _ (by simp [terminal21Domain])
  have hs1 : ({ a := 12500000, b := 12500000, c := 38828349 } : Halfplane).contains p :=
    hp _ (by simp [terminal21Domain])
  have hs2 : ({ a := -100000000, b := 0, c := -51149897 } : Halfplane).contains p :=
    hp _ (by simp [terminal21Domain])
  have hs3 : ({ a := 0, b := -100000000, c := -246852147 } : Halfplane).contains p :=
    hp _ (by simp [terminal21Domain])
  have hs4 : ({ a := 100000000, b := -100000000, c := -192640313 } : Halfplane).contains p :=
    hp _ (by simp [terminal21Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs3 ⊢
    linarith only [hs0, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal21_cover_cert :
    PolygonCoverCert [terminal21Triangle0] terminal21Domain :=
  PolygonCoverCert.leaf _ terminal21Triangle0 (by simp) terminal21_leaf0
theorem terminal21_polygon_cover :
    terminal21Domain.carrier ⊆ ⋃ K ∈ [terminal21Triangle0], Polygon.carrier K :=
  terminal21_cover_cert.sound

/-- Archived far15 terminal step 7, row 22; interval ['3/128', '7/256']. -/
def terminal22Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 56681551 },
    { a := 50000000, b := 50000000, c := 154357363 },
    { a := 0, b := 100000000, c := 257197011 },
    { a := -50000000, b := 0, c := -25758857 },
    { a := -6250000, b := -6250000, c := -18667227 },
    { a := 0, b := -100000000, c := -247157917 },
    { a := 100000000, b := -100000000, c := -192585113 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal22Triangle0Vertices : List QPoint :=
  [(1351459743660116242060634951469001976634221/3347358776493487720839180600742000000000000, 8512841433988289936940349852255921818436371/3347358776493487720839180600742000000000000), (10849751560336365655141295714378477057/25425138766651610811963518000000000000, 815575223513413281169131947621166631/397267793228931418936929968750000000), (7378142274491924096667401933826938113376371/3347358776493487720839180600742000000000000, 10445771155317170981090003724435342407245779/3347358776493487720839180600742000000000000)]
def terminal22Triangle0 : Polygon :=
  [ { a := -3209131560714230848489559862651024234013035580039490416820411149250000000000000, b := -150535352935690483221498200982933131968896738044585909320187832832000000000000, c := -1678486257768601835635734762055546526407613620968343738301688896340103557965791 },
    { a := 90863716680257029406559729139630553933043196453822670256863696117594000000000000, b := -151272280060789863325507990195777956802356737684263596348822731056884000000000000, c := -271781500325161847413780624435480936633703111032381188276607273682800454269278061 },
    { a := -3235104633517670714057644673883817413950707859232056459498161183990690368000000000000, b := 10086734331359918214212593557867806543828645444034217597150274047876337650000000000000, c := 24345958026129137029565803576019122458624421343107453285738968029395027215254754593241 } ]
private theorem terminal22_leaf0 :
    Polygon.carrier (terminal22Domain) ⊆ terminal22Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal22Triangle0, l.contains p
  intro l hl
  simp only [terminal22Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 56681551 } : Halfplane).contains p :=
    hp _ (by simp [terminal22Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 154357363 } : Halfplane).contains p :=
    hp _ (by simp [terminal22Domain])
  have hs2 : ({ a := 0, b := 100000000, c := 257197011 } : Halfplane).contains p :=
    hp _ (by simp [terminal22Domain])
  have hs3 : ({ a := -50000000, b := 0, c := -25758857 } : Halfplane).contains p :=
    hp _ (by simp [terminal22Domain])
  have hs4 : ({ a := -6250000, b := -6250000, c := -18667227 } : Halfplane).contains p :=
    hp _ (by simp [terminal22Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -247157917 } : Halfplane).contains p :=
    hp _ (by simp [terminal22Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -192585113 } : Halfplane).contains p :=
    hp _ (by simp [terminal22Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs3 hs4 ⊢
    linarith only [hs3, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal22_cover_cert :
    PolygonCoverCert [terminal22Triangle0] terminal22Domain :=
  PolygonCoverCert.leaf _ terminal22Triangle0 (by simp) terminal22_leaf0
theorem terminal22_polygon_cover :
    terminal22Domain.carrier ⊆ ⋃ K ∈ [terminal22Triangle0], Polygon.carrier K :=
  terminal22_cover_cert.sound

/-- Archived far15 terminal step 7, row 23; interval ['7/256', '1/32']. -/
def terminal23Domain : Polygon :=
  [ { a := 12500000, b := 0, c := 7100927 },
    { a := 25000000, b := 25000000, c := 77194327 },
    { a := -25000000, b := 0, c := -12970581 },
    { a := 0, b := -100000000, c := -247479377 },
    { a := 100000000, b := -100000000, c := -192523873 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal23Triangle0Vertices : List QPoint :=
  [(63054365531050254227948754814225970066649/157587505521788566096666968372400000000000, 400133209803886910146699081863681328885671/157587505521788566096666968372400000000000), (60318957594144254028964460512528183/141280926020431348621176400000000000, 9046927439778360200495961829675327/4415028938138479644411762500000000), (346713656656967082276469201357103659553671/157587505521788566096666968372400000000000, 492337605741860833859577762032733818069351/157587505521788566096666968372400000000000)]
def terminal23Triangle0 : Polygon :=
  [ { a := -10909343120739311501377994518110377397055494409683271971097034570800000000000, b := -597134911078190599892906643580324816167653938016922774663853465600000000000, c := -5881273483107932895238345376956895873971686831506204521585706745355304550657 },
    { a := 7978688520670255388400192987093497077895337106101563537964771907600000000000, b := -13159504137830154444138070264998459311443722169865857995619439738400000000000, c := -23558964750080019853266180918754722200036843620387336849217006328744038398037 },
    { a := -7265130377004322468628822800501347278783463791371474930037143827121216000000000000, b := 22350580053306024273134753489345219416315794594755783760287771827131496400000000000, c := 53843806481932810750851223094429075422859845801082422862895870879389145164836586721 } ]
private theorem terminal23_leaf0 :
    Polygon.carrier (terminal23Domain) ⊆ terminal23Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal23Triangle0, l.contains p
  intro l hl
  simp only [terminal23Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 12500000, b := 0, c := 7100927 } : Halfplane).contains p :=
    hp _ (by simp [terminal23Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 77194327 } : Halfplane).contains p :=
    hp _ (by simp [terminal23Domain])
  have hs2 : ({ a := -25000000, b := 0, c := -12970581 } : Halfplane).contains p :=
    hp _ (by simp [terminal23Domain])
  have hs3 : ({ a := 0, b := -100000000, c := -247479377 } : Halfplane).contains p :=
    hp _ (by simp [terminal23Domain])
  have hs4 : ({ a := 100000000, b := -100000000, c := -192523873 } : Halfplane).contains p :=
    hp _ (by simp [terminal23Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs3 hs4 ⊢
    linarith only [hs3, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal23_cover_cert :
    PolygonCoverCert [terminal23Triangle0] terminal23Domain :=
  PolygonCoverCert.leaf _ terminal23Triangle0 (by simp) terminal23_leaf0
theorem terminal23_polygon_cover :
    terminal23Domain.carrier ⊆ ⋃ K ∈ [terminal23Triangle0], Polygon.carrier K :=
  terminal23_cover_cert.sound

/-- Archived far15 terminal step 7, row 24; interval ['1/32', '9/256']. -/
def terminal24Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 56938577 },
    { a := 100000000, b := 100000000, c := 308849027 },
    { a := -50000000, b := 50000000, c := 102180819 },
    { a := -50000000, b := 0, c := -26121847 },
    { a := 0, b := -50000000, c := -123908161 },
    { a := 100000000, b := -100000000, c := -192456603 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal24Triangle0Vertices : List QPoint :=
  [(3321325476639649408801862908529915932773/8375785916217711706528175229680000000000, 21233088910075871506893356012160155265563/8375785916217711706528175229680000000000), (2716541893624948594181202773885652773/6359192504355419813623862000000000000, 406448445995411687623789777140477677/198724765761106869175745687500000000), (18393836271250698965863281781162191063163/8375785916217711706528175229680000000000, 26197793031933108937463285094385027422427/8375785916217711706528175229680000000000)]
def terminal24Triangle0 : Polygon :=
  [ { a := -26086894412884451905316963422914436497223468872738192858423252998480000000000, b := -1632225257867687081350998921725411083188656511603977852335374576640000000000, c := -14482253039279427008558910662197726182904299630854293322195622657663767689927 },
    { a := 57658403650941452945633595673550307695249172603230675598380741766480000000000, b := -94216772409039051834950803611374024598446139030281902992129991603360000000000, c := -168069275095242249815037925743835146703783797487848465732347203597473037455161 },
    { a := -20791649431019935620206322324664757528606895233316097253422140094261760000000000, b := 63122061817771329812386092298343182069882886047728908964257345098987600000000000, c := 151773281758076208525299949936886698588938618370402462176502570178687613983627849 } ]
private theorem terminal24_leaf0 :
    Polygon.carrier (terminal24Domain) ⊆ terminal24Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal24Triangle0, l.contains p
  intro l hl
  simp only [terminal24Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 56938577 } : Halfplane).contains p :=
    hp _ (by simp [terminal24Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 308849027 } : Halfplane).contains p :=
    hp _ (by simp [terminal24Domain])
  have hs2 : ({ a := -50000000, b := 50000000, c := 102180819 } : Halfplane).contains p :=
    hp _ (by simp [terminal24Domain])
  have hs3 : ({ a := -50000000, b := 0, c := -26121847 } : Halfplane).contains p :=
    hp _ (by simp [terminal24Domain])
  have hs4 : ({ a := 0, b := -50000000, c := -123908161 } : Halfplane).contains p :=
    hp _ (by simp [terminal24Domain])
  have hs5 : ({ a := 100000000, b := -100000000, c := -192456603 } : Halfplane).contains p :=
    hp _ (by simp [terminal24Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs3 hs5 ⊢
    linarith only [hs3, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal24_cover_cert :
    PolygonCoverCert [terminal24Triangle0] terminal24Domain :=
  PolygonCoverCert.leaf _ terminal24Triangle0 (by simp) terminal24_leaf0
theorem terminal24_polygon_cover :
    terminal24Domain.carrier ⊆ ⋃ K ∈ [terminal24Triangle0], Polygon.carrier K :=
  terminal24_cover_cert.sound

/-- Archived far15 terminal step 7, row 25; interval ['9/256', '5/128']. -/
def terminal25Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 57075019 },
    { a := 10000000, b := 10000000, c := 30892987 },
    { a := 0, b := 4000000, c := 10253123 },
    { a := -50000000, b := 0, c := -26300897 },
    { a := -50000000, b := -50000000, c := -150385171 },
    { a := 0, b := -100000000, c := -248168547 },
    { a := 50000000, b := -50000000, c := -96191657 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal25Triangle0Vertices : List QPoint :=
  [(5269334172313438148154237646974921818978453/13408394172672920915436636154198000000000000, 33936220224898983079250569032219268892232171/13408394172672920915436636154198000000000000), (10876017182997851609674920324241091513/25443748767883720320014606000000000000, 42715552144511902777787416655352337/20924135499904375263169906250000000), (29390996777454304079217118161007221953092171/13408394172672920915436636154198000000000000, 41986407623379828125164644777840319088741547/13408394172672920915436636154198000000000000)]
def terminal25Triangle0 : Polygon :=
  [ { a := -167004357618216790889046825473925409585158041778583887960387043646810000000000000, b := -11758310564031325350122641502559790830425938781643604519845137837056000000000000, c := -95390571669155783844727465615057445316957416081236247600962667202687450600956947 },
    { a := 371831303319546843883104189549503424105003679151259149661277579592666000000000000, b := -601987212624828393441370272265504546100875401416285075043263487128052000000000000, c := -1069985538234430236763311883410844952340235844657096098546659064417253574932219821 },
    { a := -2158801716054310876817831367297348791318709580207526716017536122009775208960000000000, b := 6468655206199061905424038920977532706804605945928259574694469269054301763280000000000, c := 15523578536128576275713503794100178600328541787469711644759673658165474159408140310929 } ]
private theorem terminal25_leaf0 :
    Polygon.carrier (terminal25Domain) ⊆ terminal25Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal25Triangle0, l.contains p
  intro l hl
  simp only [terminal25Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 57075019 } : Halfplane).contains p :=
    hp _ (by simp [terminal25Domain])
  have hs1 : ({ a := 10000000, b := 10000000, c := 30892987 } : Halfplane).contains p :=
    hp _ (by simp [terminal25Domain])
  have hs2 : ({ a := 0, b := 4000000, c := 10253123 } : Halfplane).contains p :=
    hp _ (by simp [terminal25Domain])
  have hs3 : ({ a := -50000000, b := 0, c := -26300897 } : Halfplane).contains p :=
    hp _ (by simp [terminal25Domain])
  have hs4 : ({ a := -50000000, b := -50000000, c := -150385171 } : Halfplane).contains p :=
    hp _ (by simp [terminal25Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -248168547 } : Halfplane).contains p :=
    hp _ (by simp [terminal25Domain])
  have hs6 : ({ a := 50000000, b := -50000000, c := -96191657 } : Halfplane).contains p :=
    hp _ (by simp [terminal25Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs3 hs4 ⊢
    linarith only [hs3, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal25_cover_cert :
    PolygonCoverCert [terminal25Triangle0] terminal25Domain :=
  PolygonCoverCert.leaf _ terminal25Triangle0 (by simp) terminal25_leaf0
theorem terminal25_polygon_cover :
    terminal25Domain.carrier ⊆ ⋃ K ∈ [terminal25Triangle0], Polygon.carrier K :=
  terminal25_cover_cert.sound

/-- Archived far15 terminal step 7, row 26; interval ['5/128', '11/256']. -/
def terminal26Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28608363 },
    { a := 50000000, b := 50000000, c := 154509911 },
    { a := 0, b := 100000000, c := 256063227 },
    { a := -50000000, b := 0, c := -26478297 },
    { a := 0, b := -50000000, c := -124267923 },
    { a := 6250000, b := -6250000, c := -12019001 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal26Triangle0Vertices : List QPoint :=
  [(1306314381123127542119792907867938921968653/3354087185218954449256035364966000000000000, 8475288269561853474720914655148195170712179/3354087185218954449256035364966000000000000), (1209662354715570824895992286483390467/2827944770562640660929914000000000000, 12862210568964456359298105574333279/6312376720005894332432843750000000), (7338308290997286994498342838930718657332179/3354087185218954449256035364966000000000000, 10514629718803648312224845666141284613271347/3354087185218954449256035364966000000000000)]
def terminal26Triangle0 : Polygon :=
  [ { a := -4640490052876072467003943182272855800055998320751580999939527648334000000000000, b := -363128079585360532848042269855178450376741561096285412000892193280000000000000, c := -2724900558657522251991021568702068483105252355151185260738695284840016438369817 },
    { a := 3469211679883681021333118950213204832141887494486697049466124599962000000000000, b := -5565005851302988362942918414605298353320596537232202650465701907828000000000000, c := -9855388142975083271726286241638225604541080834031122456685833131914707479868173 },
    { a := -136802580423755098294696691595192949557874349512492815857359001438586165760000000000, b := 404636669488553901726435361941626196139151070455374191996588865521892602320000000000, c := 969177323265199327361329575009326462362480499025111605839200943034769626722797736449 } ]
private theorem terminal26_leaf0 :
    Polygon.carrier (terminal26Domain) ⊆ terminal26Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal26Triangle0, l.contains p
  intro l hl
  simp only [terminal26Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 28608363 } : Halfplane).contains p :=
    hp _ (by simp [terminal26Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 154509911 } : Halfplane).contains p :=
    hp _ (by simp [terminal26Domain])
  have hs2 : ({ a := 0, b := 100000000, c := 256063227 } : Halfplane).contains p :=
    hp _ (by simp [terminal26Domain])
  have hs3 : ({ a := -50000000, b := 0, c := -26478297 } : Halfplane).contains p :=
    hp _ (by simp [terminal26Domain])
  have hs4 : ({ a := 0, b := -50000000, c := -124267923 } : Halfplane).contains p :=
    hp _ (by simp [terminal26Domain])
  have hs5 : ({ a := 6250000, b := -6250000, c := -12019001 } : Halfplane).contains p :=
    hp _ (by simp [terminal26Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs3 hs4 ⊢
    linarith only [hs3, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
theorem terminal26_cover_cert :
    PolygonCoverCert [terminal26Triangle0] terminal26Domain :=
  PolygonCoverCert.leaf _ terminal26Triangle0 (by simp) terminal26_leaf0
theorem terminal26_polygon_cover :
    terminal26Domain.carrier ⊆ ⋃ K ∈ [terminal26Triangle0], Polygon.carrier K :=
  terminal26_cover_cert.sound

/-- Archived far15 terminal step 7, row 27; interval ['11/256', '3/64']. -/
def terminal27Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 57363679 },
    { a := 50000000, b := 50000000, c := 154559433 },
    { a := -100000000, b := 100000000, c := 202502737 },
    { a := -3125000, b := 0, c := -1665877 },
    { a := 0, b := -25000000, c := -62227013 },
    { a := 100000000, b := -100000000, c := -192218723 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal27Triangle0Vertices : List QPoint :=
  [(5181887149506666823047607233918185802167589/13425121896347077427478410276918000000000000, 4838248181823200821088655513184688748323597/1917874556621011061068344325274000000000000), (5449499801413325909945920928935439581/12730016259480908069779654000000000000, 202267054321981792205259689618715469/99453252027194594295153546875000000), (4188120486310081281539768689382272538503597/1917874556621011061068344325274000000000000, 42132808834182257526302493088412437086352411/13425121896347077427478410276918000000000000)]
def terminal27Triangle0 : Polygon :=
  [ { a := -83557984088472336415503253529407537360347223726014159866480999566690000000000000, b := -7194691440078047958740591561346847248214389535617542062111457457152000000000000, c := -50402221198602947696213254895699517450106619794297163060250842087850290484667151 },
    { a := 188772479451120306294687099274394812690459525154862318925580610344418000000000000, b := -300043694103653866188903980826020670810024487372507362540020467016708000000000000, c := -529415705969829630340982396528268845234485464764571805484522290063072523969445937 },
    { a := -55479796597046590369259775933174274277969580286519313014223629040870055488000000000000, b := 162007364840933601686737275136068451326756865828972831787444663194314553810000000000000, c := 387283844704348130146533664070337155920574035787350405144070056887643157232916591617481 } ]
private theorem terminal27_leaf0 :
    Polygon.carrier (terminal27Domain) ⊆ terminal27Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal27Triangle0, l.contains p
  intro l hl
  simp only [terminal27Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 57363679 } : Halfplane).contains p :=
    hp _ (by simp [terminal27Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 154559433 } : Halfplane).contains p :=
    hp _ (by simp [terminal27Domain])
  have hs2 : ({ a := -100000000, b := 100000000, c := 202502737 } : Halfplane).contains p :=
    hp _ (by simp [terminal27Domain])
  have hs3 : ({ a := -3125000, b := 0, c := -1665877 } : Halfplane).contains p :=
    hp _ (by simp [terminal27Domain])
  have hs4 : ({ a := 0, b := -25000000, c := -62227013 } : Halfplane).contains p :=
    hp _ (by simp [terminal27Domain])
  have hs5 : ({ a := 100000000, b := -100000000, c := -192218723 } : Halfplane).contains p :=
    hp _ (by simp [terminal27Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal27_cover_cert :
    PolygonCoverCert [terminal27Triangle0] terminal27Domain :=
  PolygonCoverCert.leaf _ terminal27Triangle0 (by simp) terminal27_leaf0
theorem terminal27_polygon_cover :
    terminal27Domain.carrier ⊆ ⋃ K ∈ [terminal27Triangle0], Polygon.carrier K :=
  terminal27_cover_cert.sound

/-- Archived far15 terminal step 7, row 28; interval ['3/64', '13/256']. -/
def terminal28Domain : Polygon :=
  [ { a := 5000000, b := 0, c := 2875793 },
    { a := 12500000, b := 12500000, c := 38653373 },
    { a := -4000000, b := 0, c := -2146247 },
    { a := -20000000, b := -20000000, c := -60580743 },
    { a := 0, b := -100000000, c := -249247539 },
    { a := 12500000, b := -12500000, c := -24015931 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal28Triangle0Vertices : List QPoint :=
  [(64240243534558628136867965194905878941969/167933930491459409843853610026800000000000, 422949617288139198113682761735758238949231/167933930491459409843853610026800000000000), (1091213241415739479715865416280218639/2546933751957787089358485200000000000, 8078423450752254073337352383272903/3979583987434042327122633125000000), (366022797516762701659037500590991183025231/167933930491459409843853610026800000000000, 527616048564461697156536444906451836810031/167933930491459409843853610026800000000000)]
def terminal28Triangle0 : Polygon :=
  [ { a := -208974158202899487689026264624501720101764557638732070134933832625200000000000, b := -19636084143115529560126019903689293336459148779302052833818104166400000000000, c := -129393893331503712310642337034074887093800082154769625935875801682948914672129 },
    { a := 475552624717535424227624353179440780363921599887747057913982292785200000000000, b := -748984088346182912660958193144151480917207608920419991221848890556000000000000, c := -1316666158043399751727310985326386926405956355399850781236315769211975885611711 },
    { a := -8788522597373527878605687191990041109442563444243474867449472955334720000000000000, b := 25339765221991278004925890158463627819311572992204368289690732712625710800000000000, c := 60457509337963159710619997367504215510232186199636280936229456907642640113437478161 } ]
private theorem terminal28_leaf0 :
    Polygon.carrier (terminal28Domain) ⊆ terminal28Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal28Triangle0, l.contains p
  intro l hl
  simp only [terminal28Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 5000000, b := 0, c := 2875793 } : Halfplane).contains p :=
    hp _ (by simp [terminal28Domain])
  have hs1 : ({ a := 12500000, b := 12500000, c := 38653373 } : Halfplane).contains p :=
    hp _ (by simp [terminal28Domain])
  have hs2 : ({ a := -4000000, b := 0, c := -2146247 } : Halfplane).contains p :=
    hp _ (by simp [terminal28Domain])
  have hs3 : ({ a := -20000000, b := -20000000, c := -60580743 } : Halfplane).contains p :=
    hp _ (by simp [terminal28Domain])
  have hs4 : ({ a := 0, b := -100000000, c := -249247539 } : Halfplane).contains p :=
    hp _ (by simp [terminal28Domain])
  have hs5 : ({ a := 12500000, b := -12500000, c := -24015931 } : Halfplane).contains p :=
    hp _ (by simp [terminal28Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal28_cover_cert :
    PolygonCoverCert [terminal28Triangle0] terminal28Domain :=
  PolygonCoverCert.leaf _ terminal28Triangle0 (by simp) terminal28_leaf0
theorem terminal28_polygon_cover :
    terminal28Domain.carrier ⊆ ⋃ K ∈ [terminal28Triangle0], Polygon.carrier K :=
  terminal28_cover_cert.sound

/-- Archived far15 terminal step 7, row 29; interval ['13/256', '7/128']. -/
def terminal29Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 28756569 },
    { a := 50000000, b := 50000000, c := 154672079 },
    { a := -100000000, b := 0, c := -54000899 },
    { a := 0, b := -100000000, c := -249591711 },
    { a := 10000000, b := -10000000, c := -19243621 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 10).
def terminal29Triangle0Vertices : List QPoint :=
  [(1019450212947626604474924494454261366280473/2689025448890980357252131087335600000000000, 6761169220346447954576065887132558797853543/2689025448890980357252131087335600000000000), (404679986164161716883865462709053181/943682145811552970757254000000000000, 29875616637283535784217410768158587/14745033528305515168082093750000000), (5849634150324093737012113116337907548745543/2689025448890980357252131087335600000000000, 8457590114060373952540301197184439364703527/2689025448890980357252131087335600000000000)]
def terminal29Triangle0 : Polygon :=
  [ { a := -1238871897957723757883064709232845497749578989347030025303259039901200000000000, b := -126157816949819785306692839374663787409894156060954456735332693401600000000000, c := -786880827002853784927520537505293390319088536120816384002830695639291172484619 },
    { a := 946584669045744625320477467121292883224090452424374950575052274612400000000000, b := -1477333508579366838176614209475369228667333591866254543092990474792800000000000, c := -2587371299880113584451661052273752992428429706252679505168600577229275599368679 },
    { a := -2280859477613563967222919114319177587566489205565076576765880875043731315200000000000, b := 6494243765214878742922639433964801614754385247027405704821230048733183746000000000000, c := 15464137162328059788467474922395363015750708950626493534599118201743165020048156840289 } ]
private theorem terminal29_leaf0 :
    Polygon.carrier (terminal29Domain) ⊆ terminal29Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal29Triangle0, l.contains p
  intro l hl
  simp only [terminal29Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 28756569 } : Halfplane).contains p :=
    hp _ (by simp [terminal29Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 154672079 } : Halfplane).contains p :=
    hp _ (by simp [terminal29Domain])
  have hs2 : ({ a := -100000000, b := 0, c := -54000899 } : Halfplane).contains p :=
    hp _ (by simp [terminal29Domain])
  have hs3 : ({ a := 0, b := -100000000, c := -249591711 } : Halfplane).contains p :=
    hp _ (by simp [terminal29Domain])
  have hs4 : ({ a := 10000000, b := -10000000, c := -19243621 } : Halfplane).contains p :=
    hp _ (by simp [terminal29Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs3 ⊢
    linarith only [hs2, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs3 ⊢
    linarith only [hs0, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal29_cover_cert :
    PolygonCoverCert [terminal29Triangle0] terminal29Domain :=
  PolygonCoverCert.leaf _ terminal29Triangle0 (by simp) terminal29_leaf0
theorem terminal29_polygon_cover :
    terminal29Domain.carrier ⊆ ⋃ K ∈ [terminal29Triangle0], Polygon.carrier K :=
  terminal29_cover_cert.sound

end
end ElevenSquare.Tasks.T07
