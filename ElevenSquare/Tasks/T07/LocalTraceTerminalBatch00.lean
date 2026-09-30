import ElevenSquare.Tasks.T07.LocalTraceCover
import Mathlib.Tactic.Linarith

/-! Generated exact polygon union certificates from far15y-self-300.json.
The emitter is untrusted; each closed split and arithmetic leaf is checked
inside Lean.  Triangle-to-semantic forbidden-center bridges are separate. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal step 7, row 0; interval ['0', '1/7936']. -/
def terminal0Domain : Polygon :=
  [ { a := -387708359002281417731, b := 0, c := -191000000000000000000 },
    { a := -12500000, b := -12500000, c := -36939651 },
    { a := 0, b := -50000000, c := -123126687 },
    { a := 20000000, b := -20000000, c := -38642293 },
    { a := 25000000, b := 0, c := 13915367 },
    { a := 100000000, b := 100000000, c := 324062339 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } ]
def terminal0Cut : Halfplane := { a := -10308429323865824880101556273364904756000000000000, b := 16024879564742685309099207391565424554000000000000, c := 36799156464434410135685888346534151078570066900433 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal0Triangle0Vertices : List QPoint :=
  [(330403858658067793119029973777731/775416718004562835462000000000000, 502188401160052732984925387283995085021891/195367891412608802099801927674000000000000), (317518111084831860124887804800399491/745175466002384884878982000000000000, 12288099318223791596654739598435998279491/5913712498194926446399601152000000000000), (966432605688359198799411762797731/775416718004562835462000000000000, 605272694398710981785940950017644132581891/195367891412608802099801927674000000000000)]
def terminal0Triangle0 : Polygon :=
  [ { a := -569097771118633375815565979914478940712687899282977648376722369284498000000000000, b := -4518645644742409051691121928741226562500000000000000000000000000000000000, c := -242491687594378336320548513630927037394356240041481674149993625334598957621082249 },
    { a := 392902881470559137820517104307867243467868331751142616235133719468166000000000000, b := -315888433707409088732656498636045978956291725275829379397158287360000000000000000, c := -488969060232769246999152545956451833244673479155679471023697300207299509868165917 },
    { a := -10308429323865824880101556273364904756000000000000, b := 16024879564742685309099207391565424554000000000000, c := 36799156464434410135685888346534151078570066900433 } ]
private theorem terminal0_leaf0 :
    Polygon.carrier (terminal0Cut :: terminal0Domain) ⊆ terminal0Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal0Triangle0, l.contains p
  intro l hl
  simp only [terminal0Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal0Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := -387708359002281417731, b := 0, c := -191000000000000000000 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs2 : ({ a := -12500000, b := -12500000, c := -36939651 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs3 : ({ a := 0, b := -50000000, c := -123126687 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs4 : ({ a := 20000000, b := -20000000, c := -38642293 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs5 : ({ a := 25000000, b := 0, c := 13915367 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs6 : ({ a := 100000000, b := 100000000, c := 324062339 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs7 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  simp only [Halfplane.contains, terminal0Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs2 hs5 ⊢
    linarith only [hs2, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal0Triangle1Vertices : List QPoint :=
  [(246884173703492772757862521737731/775416718004562835462000000000000, 734962521169032612817959129923234822681891/195367891412608802099801927674000000000000), (62227245103232446810642821988562412698109/195367891412608802099801927674000000000000, 2153168361850058745860650910037731/775416718004562835462000000000000), (157578926041752492376748749375356458758109/195367891412608802099801927674000000000000, 1570629922636191976707580209937731/775416718004562835462000000000000)]
def terminal0Triangle1 : Polygon :=
  [ { a := -1968686161222672818166132233750895165680000000000, b := -248070333800074152554244495683338240000000000, c := -627741295671431727312101335143785796623537010299 },
    { a := -1048369991565671002733815367654100805000000000000, b := -681083435275143182615042338477100329000000000000, c := -2225144412917164463461731218266440994339460233607 },
    { a := 1325528050669128671366009145665230125294123841245467117404334392661327920000000000, b := 372667899819641628421719473318294703268326904606873702442998071282466560000000000, c := 1823988313924686711727098010499202045511274986241375238287402311070942816578375631 } ]
private theorem terminal0_leaf1 :
    Polygon.carrier ((⟨-terminal0Cut.a, -terminal0Cut.b, -terminal0Cut.c⟩ : Halfplane) :: terminal0Domain) ⊆ terminal0Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal0Triangle1, l.contains p
  intro l hl
  simp only [terminal0Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal0Cut.a, -terminal0Cut.b, -terminal0Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := -387708359002281417731, b := 0, c := -191000000000000000000 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs2 : ({ a := -12500000, b := -12500000, c := -36939651 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs3 : ({ a := 0, b := -50000000, c := -123126687 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs4 : ({ a := 20000000, b := -20000000, c := -38642293 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs5 : ({ a := 25000000, b := 0, c := 13915367 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs6 : ({ a := 100000000, b := 100000000, c := 324062339 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  have hs7 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal0Domain])
  simp only [Halfplane.contains, terminal0Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
theorem terminal0_cover_cert :
    PolygonCoverCert [terminal0Triangle0, terminal0Triangle1] terminal0Domain := by
  refine PolygonCoverCert.split terminal0Domain terminal0Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal0Triangle0 (by simp) terminal0_leaf0
  · exact PolygonCoverCert.leaf _ terminal0Triangle1 (by simp) terminal0_leaf1
theorem terminal0_polygon_cover :
    terminal0Domain.carrier ⊆ ⋃ K ∈ [terminal0Triangle0, terminal0Triangle1], Polygon.carrier K :=
  terminal0_cover_cert.sound

/-- Archived far15 terminal step 7, row 1; interval ['1/7936', '1/3968']. -/
def terminal1Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55664337 },
    { a := 6250000, b := 6250000, c := 20254583 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -100000000, b := 0, c := -49276247 },
    { a := 0, b := -50000000, c := -123120529 },
    { a := 2000000, b := -2000000, c := -3864217 } ]
def terminal1Cut : Halfplane := { a := -38189758785272060721944700576519840421362796000000000000, b := 59367558908679028179150040184395371407029414000000000000, c := 136327633716158826889525076073963635079578974469459338569 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal1Triangle0Vertices : List QPoint :=
  [(308312438235946086837712046183716884914258275797/723781714267672898063120239769413334000000000000, 1860373377483110169372872170064928003754780517547/723781714267672898063120239769413334000000000000), (3332887203550930867497088583888210102095359/7821870646004311380566167416706000000000000, 8191577002975303494978103930397047924607/3942475123994108558753108576968750000000), (901988027322736368629212448027670598984552415797/723781714267672898063120239769413334000000000000, 2242270965335830776592319175830126407968408477547/723781714267672898063120239769413334000000000000)]
def terminal1Triangle0 : Polygon :=
  [ { a := -14600184496005866577062283000412167616092702099474154952684008546116963950890000000000000, b := -3679597963975054112727176912721906365704658848003168111712558337185240064000000000000, c := -6228761818487964598228952064411847116110685260970218494235411306533608108572079615678507 },
    { a := 5775788770942168510906518701158503472173447320484333376588013759781712814379990000000000000, b := -4642950860316163177564871175209887003026842881795366412860588699094967521987776000000000000, c := -7185953285785174817011373306845757322397381418859668078853454252230685662362988788280085163 },
    { a := -38189758785272060721944700576519840421362796000000000000, b := 59367558908679028179150040184395371407029414000000000000, c := 136327633716158826889525076073963635079578974469459338569 } ]
private theorem terminal1_leaf0 :
    Polygon.carrier (terminal1Cut :: terminal1Domain) ⊆ terminal1Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal1Triangle0, l.contains p
  intro l hl
  simp only [terminal1Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal1Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55664337 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs2 : ({ a := 6250000, b := 6250000, c := 20254583 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49276247 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs5 : ({ a := 0, b := -50000000, c := -123120529 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs6 : ({ a := 2000000, b := -2000000, c := -3864217 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  simp only [Halfplane.contains, terminal1Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal1Triangle1Vertices : List QPoint :=
  [(230354329585569314237614241767892440968851995797/723781714267672898063120239769413334000000000000, 2722734384704254476790657583782733525702957577547/723781714267672898063120239769413334000000000000), (230623874205362749841565934419816905353612002453/723781714267672898063120239769413334000000000000, 2009699042617616373150474717124934261979785095797/723781714267672898063120239769413334000000000000), (583874362752797430673899156875001872160853462453/723781714267672898063120239769413334000000000000, 1465951841440370119877277197320112466328279395797/723781714267672898063120239769413334000000000000)]
def terminal1Triangle1 : Polygon :=
  [ { a := -182335360876455006857398024472800520631280250000000000000, b := -68927180213139025428347066673720770623488000000000000, c := -58290240532994371793566346794526923967658302156703619779 },
    { a := -3883908579837473237665696570034441397510755000000000000, b := -2523217775338819148802380160394178334337439000000000000, c := -8243687666512574295211896025723233279209495998639148847 },
    { a := 454818111812609999867568462834299298854954233679335827209484912276114266623662727250000000000000, b := 127935667816870473272244102729478183153040771598262894193261555553979346688341395552000000000000, c := 626023225087299661780523200660985768940279968939970107049921941690439440650318818618025728438791 } ]
private theorem terminal1_leaf1 :
    Polygon.carrier ((⟨-terminal1Cut.a, -terminal1Cut.b, -terminal1Cut.c⟩ : Halfplane) :: terminal1Domain) ⊆ terminal1Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal1Triangle1, l.contains p
  intro l hl
  simp only [terminal1Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal1Cut.a, -terminal1Cut.b, -terminal1Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55664337 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs2 : ({ a := 6250000, b := 6250000, c := 20254583 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49276247 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs5 : ({ a := 0, b := -50000000, c := -123120529 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  have hs6 : ({ a := 2000000, b := -2000000, c := -3864217 } : Halfplane).contains p :=
    hp _ (by simp [terminal1Domain])
  simp only [Halfplane.contains, terminal1Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal1_cover_cert :
    PolygonCoverCert [terminal1Triangle0, terminal1Triangle1] terminal1Domain := by
  refine PolygonCoverCert.split terminal1Domain terminal1Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal1Triangle0 (by simp) terminal1_leaf0
  · exact PolygonCoverCert.leaf _ terminal1Triangle1 (by simp) terminal1_leaf1
theorem terminal1_polygon_cover :
    terminal1Domain.carrier ⊆ ⋃ K ∈ [terminal1Triangle0, terminal1Triangle1], Polygon.carrier K :=
  terminal1_cover_cert.sound

/-- Archived far15 terminal step 7, row 2; interval ['1/3968', '3/7936']. -/
def terminal2Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55667211 },
    { a := 625000, b := 625000, c := 2025527 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -50000000, b := 50000000, c := 112536487 },
    { a := -100000000, b := 0, c := -49288657 },
    { a := -25000000, b := -25000000, c := -73879349 },
    { a := 0, b := -50000000, c := -123114369 },
    { a := 100000000, b := -100000000, c := -193210227 } ]
def terminal2Cut : Halfplane := { a := -1298451943008177146829811263104423810777014112000000000, b := 2018497227229280263070126788102554817580553008000000000, c := 4635050469605451755611094378796821028925313038831630301 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal2Triangle0Vertices : List QPoint :=
  [(52397853829132402043227727143291390598509177149/123042905100396032471358442725802256240000000000, 316248227428749205263051049034122509849219591491/123042905100396032471358442725802256240000000000), (1999732742819400622589958263887094027465419/4693122685672773229293654401616400000000000, 4914652832374181172597858995011933689107/2365485224633454248635914516943750000000), (153322715190596415196734066548419131477536827549/123042905100396032471358442725802256240000000000, 381170824579158062604541612189343700388070297091/123042905100396032471358442725802256240000000000)]
def terminal2Triangle0 : Polygon :=
  [ { a := -284440816932130913087977744591841080257126182336902506112656004117728673503135280000000000, b := -143369614814913118117637586438860012970772061904977560246465274014099233320960000000000, c := -121497689956225246241948016084555861456417248942284930928140159997685788564919468951118817 },
    { a := 589130530431509263841267470290455696405902274620359813127167799547271594034975280000000000, b := -473509386789051376717907861234977322471608907016779867865279493944467954873239040000000000, c := -732759607775456537545140851421403005020862585938518260808970743371858382023823007137749983 },
    { a := -1298451943008177146829811263104423810777014112000000000, b := 2018497227229280263070126788102554817580553008000000000, c := 4635050469605451755611094378796821028925313038831630301 } ]
private theorem terminal2_leaf0 :
    Polygon.carrier (terminal2Cut :: terminal2Domain) ⊆ terminal2Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal2Triangle0, l.contains p
  intro l hl
  simp only [terminal2Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal2Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55667211 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs2 : ({ a := 625000, b := 625000, c := 2025527 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112536487 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49288657 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs6 : ({ a := -25000000, b := -25000000, c := -73879349 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs7 : ({ a := 0, b := -50000000, c := -123114369 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs8 : ({ a := 100000000, b := -100000000, c := -193210227 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  simp only [Halfplane.contains, terminal2Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
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
def terminal2Triangle1Vertices : List QPoint :=
  [(39144973885653703615436542665192010544207396349/123042905100396032471358442725802256240000000000, 462849614949506573325197294097901703303542373091/123042905100396032471358442725802256240000000000), (39221344864899706103219163358992824926825395709/123042905100396032471358442725802256240000000000, 341633608719450524704412773286849323253833712349/123042905100396032471358442725802256240000000000), (99273934592161163578501477190737443614260961309/123042905100396032471358442725802256240000000000, 249196574245939396924227113074405072644242860349/123042905100396032471358442725802256240000000000)]
def terminal2Triangle1 : Polygon :=
  [ { a := -30997012825294699542360276109165042954990790160000000000, b := -19529369897534858273854012029439334110412800000000000, c := -9934879365204291647798547084453207058576850904152372811 },
    { a := -660264531953650912715611858660316075782791800000000000, b := -428947069480438981966302241655318704910254040000000000, c := -1401455842296232984188681284226023271587247931631446759 },
    { a := 13144245405850033429551306598637106462499561630173494010231088933992906525038114505040000000000, b := 3699221002998119684793130543844401857422053614308332912911356597482089872811702675200000000000, c := 18097054504626316740891245164238009318896877838252827438945712848090687532984781083965547135159 } ]
private theorem terminal2_leaf1 :
    Polygon.carrier ((⟨-terminal2Cut.a, -terminal2Cut.b, -terminal2Cut.c⟩ : Halfplane) :: terminal2Domain) ⊆ terminal2Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal2Triangle1, l.contains p
  intro l hl
  simp only [terminal2Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal2Cut.a, -terminal2Cut.b, -terminal2Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55667211 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs2 : ({ a := 625000, b := 625000, c := 2025527 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112536487 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49288657 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs6 : ({ a := -25000000, b := -25000000, c := -73879349 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs7 : ({ a := 0, b := -50000000, c := -123114369 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  have hs8 : ({ a := 100000000, b := -100000000, c := -193210227 } : Halfplane).contains p :=
    hp _ (by simp [terminal2Domain])
  simp only [Halfplane.contains, terminal2Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs6 ⊢
    linarith only [hs4, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs4 ⊢
    linarith only [hs1, hs4]
theorem terminal2_cover_cert :
    PolygonCoverCert [terminal2Triangle0, terminal2Triangle1] terminal2Domain := by
  refine PolygonCoverCert.split terminal2Domain terminal2Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal2Triangle0 (by simp) terminal2_leaf0
  · exact PolygonCoverCert.leaf _ terminal2Triangle1 (by simp) terminal2_leaf1
theorem terminal2_polygon_cover :
    terminal2Domain.carrier ⊆ ⋃ K ∈ [terminal2Triangle0, terminal2Triangle1], Polygon.carrier K :=
  terminal2_cover_cert.sound

/-- Archived far15 terminal step 7, row 3; interval ['3/7936', '1/1984']. -/
def terminal3Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55670091 },
    { a := 20000000, b := 20000000, c := 64819063 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -20000000, b := 0, c := -9860213 },
    { a := 0, b := -20000000, c := -49243283 },
    { a := 100000000, b := -100000000, c := -193209599 } ]
def terminal3Cut : Halfplane := { a := -129845216977936447817105825591166432884751330400000000000, b := 201849757975446635763269199337996748743612423600000000000, c := 463496158345785338595675240813148400987214440274640393141 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal3Triangle0Vertices : List QPoint :=
  [(1047652006684366553209169952042636957891886544593/2460858531790260035377510468390106231600000000000, 6324659938397493490680810913434802839337854933423/2460858531790260035377510468390106231600000000000), (4999333434631659439318789835545864941944311/11732807831945132076811463322514000000000000, 6142949523820642331868607187119392643531/2956856812486172398389985716359375000000), (3066149586438832910841861945422604445328010780593/2460858531790260035377510468390106231600000000000, 7623112108176857968851869169346467168185368237423/2460858531790260035377510468390106231600000000000)]
def terminal3Triangle0 : Polygon :=
  [ { a := -14222042427289586756691251686203584088403355649300363012613364210161224232755969200000000000, b := -10752666698253633229987092871544280380103645543533014354767343265029339401625600000000000, c := -6082331858999048116236345152299050477772328347666874123288950517808565749970818411470366809 },
    { a := 9818844071427688214747931357250101954815875428488190930478200785430627319670656400000000000, b := -7890630515269081038140386420027836671601098613224427076138013505542136836634124800000000000, c := -12209200953670625804307949249733552712057510479962577734784619555119257121126927323741992397 },
    { a := -129845216977936447817105825591166432884751330400000000000, b := 201849757975446635763269199337996748743612423600000000000, c := 463496158345785338595675240813148400987214440274640393141 } ]
private theorem terminal3_leaf0 :
    Polygon.carrier (terminal3Cut :: terminal3Domain) ⊆ terminal3Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal3Triangle0, l.contains p
  intro l hl
  simp only [terminal3Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal3Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55670091 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs2 : ({ a := 20000000, b := 20000000, c := 64819063 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs4 : ({ a := -20000000, b := 0, c := -9860213 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs5 : ({ a := 0, b := -20000000, c := -49243283 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193209599 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  simp only [Halfplane.contains, terminal3Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs6 ⊢
    linarith only [hs1, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal3Triangle1Vertices : List QPoint :=
  [(782594361523186083149478818448410281947864872593/2460858531790260035377510468390106231600000000000, 9256688200883509419985297296386397110733825577423/2460858531790260035377510468390106231600000000000), (784732749111841064807219894076758726762626514577/2460858531790260035377510468390106231600000000000, 6832368114775875227530538171809983505176123812593/2460858531790260035377510468390106231600000000000), (1985784753417579998343045130027159748489969718577/2460858531790260035377510468390106231600000000000, 4983627102427995569229880954717411463278343632593/2460858531790260035377510468390106231600000000000)]
def terminal3Triangle1 : Polygon :=
  [ { a := -619940305716210457849414288662842472550259586000000000000, b := -546822452632050101941165846160028725511372800000000000, c := -199208343895774071195550651960563126974932513152268888639 },
    { a := -1886470420763142508470058384788338818263041000000000000, b := -1225563269699733605648801261173878593599329800000000000, c := -4004242583896898498870235509354526697109869707365265349 },
    { a := 5257699430497655799227922608615688538379241104031075311293485956365833835349735201314000000000000, b := 1480440670630692899471461297146976285697602981958611131204371596292869282355458316947200000000000, c := 7240815913080299447158259347265669633260148302898482609063281430586055632803654409745857543831711 } ]
private theorem terminal3_leaf1 :
    Polygon.carrier ((⟨-terminal3Cut.a, -terminal3Cut.b, -terminal3Cut.c⟩ : Halfplane) :: terminal3Domain) ⊆ terminal3Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal3Triangle1, l.contains p
  intro l hl
  simp only [terminal3Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal3Cut.a, -terminal3Cut.b, -terminal3Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55670091 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs2 : ({ a := 20000000, b := 20000000, c := 64819063 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs4 : ({ a := -20000000, b := 0, c := -9860213 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs5 : ({ a := 0, b := -20000000, c := -49243283 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  have hs6 : ({ a := 100000000, b := -100000000, c := -193209599 } : Halfplane).contains p :=
    hp _ (by simp [terminal3Domain])
  simp only [Halfplane.contains, terminal3Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal3_cover_cert :
    PolygonCoverCert [terminal3Triangle0, terminal3Triangle1] terminal3Domain := by
  refine PolygonCoverCert.split terminal3Domain terminal3Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal3Triangle0 (by simp) terminal3_leaf0
  · exact PolygonCoverCert.leaf _ terminal3Triangle1 (by simp) terminal3_leaf1
theorem terminal3_polygon_cover :
    terminal3Domain.carrier ⊆ ⋃ K ∈ [terminal3Triangle0, terminal3Triangle1], Polygon.carrier K :=
  terminal3_cover_cert.sound

/-- Archived far15 terminal step 7, row 4; interval ['1/1984', '5/7936']. -/
def terminal4Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 55672977 },
    { a := 12500000, b := 12500000, c := 40513289 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := 0, b := 25000000, c := 68589733 },
    { a := -100000000, b := 0, c := -49313469 },
    { a := -100000000, b := -100000000, c := -295517559 },
    { a := 0, b := -100000000, c := -246204089 },
    { a := 25000000, b := -25000000, c := -48302241 } ]
def terminal4Cut : Halfplane := { a := -40576639969151051915237453932995664883093132000000000000, b := 63078064389708713253020005671496892548880438000000000000, c := 144839777746816008359549633057151138092857602662594879649 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal4Triangle0Vertices : List QPoint :=
  [(327295962586977224251823071058279507758269869133/769018474330358422896357593048719078000000000000, 1976361141525332731009142181872890577473417351731/769018474330358422896357593048719078000000000000), (1666445179358623316592438467772234924328443/3910936440765354693860411026826000000000000, 2047527734096741739865809425953737513299/985619062692881727283369714421875000000), (958076606484064356782023127773248433247074249133/769018474330358422896357593048719078000000000000, 2382127541216843250161516721202847226304348671731/769018474330358422896357593048719078000000000000)]
def terminal4Triangle0 : Polygon :=
  [ { a := -1481462964542523208607824588167089428457540861103106972313983205200841325834110000000000000, b := -1493422388765605938877391759277178261076563490496417939478105767439339773696000000000000, c := -634351976288646098216781804350976941497681718957663344423586117163708512858972258766709377 },
    { a := 3068389563534211675218901299263028001179483872838740743879355474711924916154110000000000000, b := -2465449583957786997131519477966721253507102307008464382836981294795406958106304000000000000, c := -3814294705442136098428105167710464100053517890212602556561368063374581370724800781790690623 },
    { a := -40576639969151051915237453932995664883093132000000000000, b := 63078064389708713253020005671496892548880438000000000000, c := 144839777746816008359549633057151138092857602662594879649 } ]
private theorem terminal4_leaf0 :
    Polygon.carrier (terminal4Cut :: terminal4Domain) ⊆ terminal4Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal4Triangle0, l.contains p
  intro l hl
  simp only [terminal4Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal4Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55672977 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs2 : ({ a := 12500000, b := 12500000, c := 40513289 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs4 : ({ a := 0, b := 25000000, c := 68589733 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49313469 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517559 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246204089 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs8 : ({ a := 25000000, b := -25000000, c := -48302241 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  simp only [Halfplane.contains, terminal4Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs6 ⊢
    linarith only [hs1, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal4Triangle1Vertices : List QPoint :=
  [(244465428747569430129541674598405944123955109133/769018474330358422896357593048719078000000000000, 2892620191764253084256820390325662552486943371731/769018474330358422896357593048719078000000000000), (245324602427790766116930007312664832240527488269/769018474330358422896357593048719078000000000000, 2135020176884856561352499167624219358427477809133/769018474330358422896357593048719078000000000000), (620653443159924281480672437199151442143988308269/769018474330358422896357593048719078000000000000, 1557288472936219271587094761988948584531860909133/769018474330358422896357593048719078000000000000)]
def terminal4Triangle1 : Polygon :=
  [ { a := -7749254682636064639786101697487360155665625360000000000, b := -8788220081691443199511911156145873828331520000000000, c := -2496488596056755256037252178967692369972126016988539483 },
    { a := -4126655028204552069752888611680505527825835000000000000, b := -2680920290943810824026731642046332927881863000000000000, c := -8759463059455993155899743381921825540139440769814035223 },
    { a := 20537895222761394234303718676574207979485658862853578432939630534306979392114880892880000000000, b := 5785910658095120273726424127170418760679357186762398602806983006516429652785926332160000000000, c := 28292229751048072192822535617166256496569614880102025891194488966356660520494525992983837534639 } ]
private theorem terminal4_leaf1 :
    Polygon.carrier ((⟨-terminal4Cut.a, -terminal4Cut.b, -terminal4Cut.c⟩ : Halfplane) :: terminal4Domain) ⊆ terminal4Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal4Triangle1, l.contains p
  intro l hl
  simp only [terminal4Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal4Cut.a, -terminal4Cut.b, -terminal4Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 100000000, b := 0, c := 55672977 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs2 : ({ a := 12500000, b := 12500000, c := 40513289 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs4 : ({ a := 0, b := 25000000, c := 68589733 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs5 : ({ a := -100000000, b := 0, c := -49313469 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517559 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs7 : ({ a := 0, b := -100000000, c := -246204089 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  have hs8 : ({ a := 25000000, b := -25000000, c := -48302241 } : Halfplane).contains p :=
    hp _ (by simp [terminal4Domain])
  simp only [Halfplane.contains, terminal4Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal4_cover_cert :
    PolygonCoverCert [terminal4Triangle0, terminal4Triangle1] terminal4Domain := by
  refine PolygonCoverCert.split terminal4Domain terminal4Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal4Triangle0 (by simp) terminal4_leaf0
  · exact PolygonCoverCert.leaf _ terminal4Triangle1 (by simp) terminal4_leaf1
theorem terminal4_polygon_cover :
    terminal4Domain.carrier ⊆ ⋃ K ∈ [terminal4Triangle0, terminal4Triangle1], Polygon.carrier K :=
  terminal4_cover_cert.sound

/-- Archived far15 terminal step 7, row 5; interval ['5/7936', '3/3968']. -/
def terminal5Domain : Polygon :=
  [ { a := 25000000, b := 0, c := 13918967 },
    { a := 100000000, b := 100000000, c := 324117313 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := 0, b := 100000000, c := 274357583 },
    { a := -10000000, b := 0, c := -4932587 },
    { a := -100000000, b := -100000000, c := -295517631 },
    { a := 0, b := -1250000, c := -3077397 },
    { a := 100000000, b := -100000000, c := -193208323 } ]
def terminal5Cut : Halfplane := { a := -649226435354307077215446305445188109042853516000000000000, b := 1009249334688981728265878766703781513726755894000000000000, c := 2317392191458871967474919305521869263137084919645371223073 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal5Triangle0Vertices : List QPoint :=
  [(5235211486677528159661995158712283454073405915597/12304299301043186165516833355687914214000000000000, 31620258459983417301500710900677923479250746248371/12304299301043186165516833355687914214000000000000), (9998676334762266175700944726060509123573203/23465622370469458175086890555866000000000000, 2233533482136900046885013460360137018357/1075220966388813149518277609781250000000), (15327704833567345442320782825750098591340964855597/12304299301043186165516833355687914214000000000000, 38112522813526488073655173955129804569679281408371/12304299301043186165516833355687914214000000000000)]
def terminal5Triangle0 : Polygon :=
  [ { a := -142220469435621526019487759119797007264945367487473015060379701518583830530084334000000000000, b := -179210461253523607596360428666049056302753021210847123819339167319677803965440000000000000, c := -60972258393454389338330242676410271572919177291652251432965519237360845249983985870891251017 },
    { a := 294565493085123242864644701712781445878698179875544218518413304150784355778644334000000000000, b := -236647427193338346254281778432642234056512974769674224465777322621345839938074560000000000000, c := -366068593204944765870333401716294952132088302512588630363966431964016583922342766699313188983 },
    { a := -649226435354307077215446305445188109042853516000000000000, b := 1009249334688981728265878766703781513726755894000000000000, c := 2317392191458871967474919305521869263137084919645371223073 } ]
private theorem terminal5_leaf0 :
    Polygon.carrier (terminal5Cut :: terminal5Domain) ⊆ terminal5Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal5Triangle0, l.contains p
  intro l hl
  simp only [terminal5Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal5Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 25000000, b := 0, c := 13918967 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324117313 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs4 : ({ a := 0, b := 100000000, c := 274357583 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs5 : ({ a := -10000000, b := 0, c := -4932587 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517631 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs7 : ({ a := 0, b := -1250000, c := -3077397 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs8 : ({ a := 100000000, b := -100000000, c := -193208323 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  simp only [Halfplane.contains, terminal5Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs8 ⊢
    linarith only [hs1, hs8]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal5Triangle1Vertices : List QPoint :=
  [(3909922545455761182822153037734484513073710035597/12304299301043186165516833355687914214000000000000, 46280407686237424721678062409744304044103642508371/12304299301043186165516833355687914214000000000000), (3926724166492189826128643565034209866597772671629/12304299301043186165516833355687914214000000000000, 34158807640635574687013578228465978326001335135597/12304299301043186165516833355687914214000000000000), (9931987429774796550648491734476302234414741331629/12304299301043186165516833355687914214000000000000, 24915097588967857160927342001080241641067305435597/12304299301043186165516833355687914214000000000000)]
def terminal5Triangle1 : Polygon :=
  [ { a := -123988092637980625326998487595682875788492731280000000000, b := -171858577885418556720793197538901145476055040000000000, c := -40045963753534237638230492321472176710651690274359144851 },
    { a := -66026500369055125186330258767040976320957355000000000000, b := -42894737594875762317998915496014945484406919000000000000, c := -140154339774615804919675488771827549478976297855150338967 },
    { a := 5257703401928097359289930373332271858983784708255837712086899290519487172152527740192720000000000, b := 1481945774939268452563744177841566813830798341743985547344773479997516066346385091976960000000000, c := 7244806511984541530836323382835514587722765470813300751230510500904536002584914349008668637172399 } ]
private theorem terminal5_leaf1 :
    Polygon.carrier ((⟨-terminal5Cut.a, -terminal5Cut.b, -terminal5Cut.c⟩ : Halfplane) :: terminal5Domain) ⊆ terminal5Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal5Triangle1, l.contains p
  intro l hl
  simp only [terminal5Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal5Cut.a, -terminal5Cut.b, -terminal5Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 25000000, b := 0, c := 13918967 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs2 : ({ a := 100000000, b := 100000000, c := 324117313 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs4 : ({ a := 0, b := 100000000, c := 274357583 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs5 : ({ a := -10000000, b := 0, c := -4932587 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs6 : ({ a := -100000000, b := -100000000, c := -295517631 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs7 : ({ a := 0, b := -1250000, c := -3077397 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  have hs8 : ({ a := 100000000, b := -100000000, c := -193208323 } : Halfplane).contains p :=
    hp _ (by simp [terminal5Domain])
  simp only [Halfplane.contains, terminal5Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal5_cover_cert :
    PolygonCoverCert [terminal5Triangle0, terminal5Triangle1] terminal5Domain := by
  refine PolygonCoverCert.split terminal5Domain terminal5Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal5Triangle0 (by simp) terminal5_leaf0
  · exact PolygonCoverCert.leaf _ terminal5Triangle1 (by simp) terminal5_leaf1
theorem terminal5_polygon_cover :
    terminal5Domain.carrier ⊆ ⋃ K ∈ [terminal5Triangle0, terminal5Triangle1], Polygon.carrier K :=
  terminal5_cover_cert.sound

/-- Archived far15 terminal step 7, row 6; interval ['3/3968', '7/7936']. -/
def terminal6Domain : Polygon :=
  [ { a := 20000000, b := 0, c := 11135753 },
    { a := 25000000, b := 25000000, c := 81032079 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -50000000, b := 50000000, c := 112508983 },
    { a := -25000000, b := 0, c := -12334567 },
    { a := 0, b := -25000000, c := -61544857 },
    { a := 4000000, b := -4000000, c := -7728307 } ]
def terminal6Cut : Halfplane := { a := -162306668108342908923265482386183392094391308000000000000, b := 252312425809547282594971651464394116990412022000000000000, c := 579337008563534024431151906346978373557122538711357007937 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal6Triangle0Vertices : List QPoint :=
  [(1308422072283623758276005809961508916981494965101/3076075948556001991109074505832182182000000000000, 7904685069644198581973663362377447026655293672211/3076075948556001991109074505832182182000000000000), (9998682645094897707076521429373028616696257/23465626841522254189396199829758000000000000, 1889800352178274479962364123540580130857/909802529525521641958599559156250000000), (3831546330379096584225722324605450086885615185101/3076075948556001991109074505832182182000000000000, 9527751750727627671206318186239280947599206752211/3076075948556001991109074505832182182000000000000)]
def terminal6Triangle0 : Polygon :=
  [ { a := -35555124697877472277175095350785166919547159079078874489280149900887978464445530000000000000, b := -53763102401949737703630115308699363023424755364431144641798495320167430217216000000000000, c := -15261681153351163456162217464378563073569782564277233277141215843256891775624741190018216083 },
    { a := 24547133925029742082552757040784296570611553553067181428317896671283442633028510000000000000, b := -19717643070953033720548566097954916617196903680926890664704994289675532692180928000000000000, c := -30497077753155290401703783038689885695768971080025385806357020186673815907875961793314634639 },
    { a := -162306668108342908923265482386183392094391308000000000000, b := 252312425809547282594971651464394116990412022000000000000, c := 579337008563534024431151906346978373557122538711357007937 } ]
private theorem terminal6_leaf0 :
    Polygon.carrier (terminal6Cut :: terminal6Domain) ⊆ terminal6Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal6Triangle0, l.contains p
  intro l hl
  simp only [terminal6Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal6Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 20000000, b := 0, c := 11135753 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs2 : ({ a := 25000000, b := 25000000, c := 81032079 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112508983 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs5 : ({ a := -25000000, b := 0, c := -12334567 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs6 : ({ a := 0, b := -25000000, c := -61544857 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs7 : ({ a := 4000000, b := -4000000, c := -7728307 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  simp only [Halfplane.contains, terminal6Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs6 ⊢
    linarith only [hs1, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal6Triangle1Vertices : List QPoint :=
  [(977099715988706946294802238201537956823940525101/3076075948556001991109074505832182182000000000000, 11569723714575285142351611572822746411119411052211/3076075948556001991109074505832182182000000000000), (982063832161948371998112641155771860058624287789/3076075948556001991109074505832182182000000000000, 8539323751292200246636654115163297591788976825101/3076075948556001991109074505832182182000000000000), (2483380196220518041423168073345394468284522867789/3076075948556001991109074505832182182000000000000, 6228395394490143596998937910069845862403820725101/3076075948556001991109074505832182182000000000000)]
def terminal6Triangle1 : Polygon :=
  [ { a := -774925714316556961140626137960262089208609130000000000000, b := -1269410413842502453674963994470778285410304000000000000, c := -250925671553055203552844557481192563820717283828394834507 },
    { a := -16506631120014690354555115750667512352751115000000000000, b := -10723688314704069067321824515640161487327847000000000000, c := -35039320726657966295815630337503333728490707461122770551 },
    { a := 8215165789377469200484768683610445413452515195568566778881261791090724293191246777010000000000000, b := 2316716578510229260190763013742079398490698262044704686170414466725304695184385792608000000000000, c := 11323129688748731408587329337926742899326762057241405055673518361400066489948555661571695608935639 } ]
private theorem terminal6_leaf1 :
    Polygon.carrier ((⟨-terminal6Cut.a, -terminal6Cut.b, -terminal6Cut.c⟩ : Halfplane) :: terminal6Domain) ⊆ terminal6Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal6Triangle1, l.contains p
  intro l hl
  simp only [terminal6Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal6Cut.a, -terminal6Cut.b, -terminal6Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 20000000, b := 0, c := 11135753 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs2 : ({ a := 25000000, b := 25000000, c := 81032079 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs4 : ({ a := -50000000, b := 50000000, c := 112508983 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs5 : ({ a := -25000000, b := 0, c := -12334567 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs6 : ({ a := 0, b := -25000000, c := -61544857 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  have hs7 : ({ a := 4000000, b := -4000000, c := -7728307 } : Halfplane).contains p :=
    hp _ (by simp [terminal6Domain])
  simp only [Halfplane.contains, terminal6Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs5 hs6 ⊢
    linarith only [hs5, hs6]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs5 ⊢
    linarith only [hs0, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal6_cover_cert :
    PolygonCoverCert [terminal6Triangle0, terminal6Triangle1] terminal6Domain := by
  refine PolygonCoverCert.split terminal6Domain terminal6Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal6Triangle0 (by simp) terminal6_leaf0
  · exact PolygonCoverCert.leaf _ terminal6Triangle1 (by simp) terminal6_leaf1
theorem terminal6_polygon_cover :
    terminal6Domain.carrier ⊆ ⋃ K ∈ [terminal6Triangle0, terminal6Triangle1], Polygon.carrier K :=
  terminal6_cover_cert.sound

/-- Archived far15 terminal step 7, row 7; interval ['7/7936', '1/992']. -/
def terminal7Domain : Polygon :=
  [ { a := 25000000, b := 0, c := 13920417 },
    { a := 50000000, b := 50000000, c := 162069661 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -100000000, b := 0, c := -49350663 },
    { a := -25000000, b := -25000000, c := -73879439 },
    { a := 0, b := -25000000, c := -61541773 },
    { a := 100000000, b := -100000000, c := -193207021 } ]
def terminal7Cut : Halfplane := { a := -1527592825279136684084939327821515802409213920000000000, b := 2374706202077639358063952188919832236615335280000000000, c := 5452479934895563680742241246905311586849678861972738809 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal7Triangle0Vertices : List QPoint :=
  [(8793555980869959366866184696966857399618106399/20679511040048114610299922706532981200000000000, 371967337882830809943691051858522095739067918247/144756577280336802272099458945730868400000000000), (166644833452493908228022681942849467088997/391093867629175270101506566377200000000000, 818864721119863468323882324588098455241/394247850432636360989421941912500000000), (25755743138567383353037271760679944804013358399/20679511040048114610299922706532981200000000000, 448346979146787644147938018249597885859528614247/144756577280336802272099458945730868400000000000)]
def terminal7Triangle0 : Polygon :=
  [ { a := -27886378953675016533251173905947671892149398081306772123164929937090822970643600000000000, b := -49194980630101247319427825540018373958786072096698835450321912332893921075200000000000, c := -11984546744654872468161993215639403877405155970642647338317477417859019122239798281596163 },
    { a := 1343209029388949859669167566732125945658041241327438773882123943243221709345200000000000, b := -1078778062140618374342048505996543705474305769173383057582560498390808219993600000000000, c := -1668314232564773437666555925499390571382889132657224454561156188027864935644772651151159 },
    { a := -1527592825279136684084939327821515802409213920000000000, b := 2374706202077639358063952188919832236615335280000000000, c := 5452479934895563680742241246905311586849678861972738809 } ]
private theorem terminal7_leaf0 :
    Polygon.carrier (terminal7Cut :: terminal7Domain) ⊆ terminal7Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal7Triangle0, l.contains p
  intro l hl
  simp only [terminal7Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal7Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 25000000, b := 0, c := 13920417 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs2 : ({ a := 50000000, b := 50000000, c := 162069661 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49350663 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs5 : ({ a := -25000000, b := -25000000, c := -73879439 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs6 : ({ a := 0, b := -25000000, c := -61541773 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs7 : ({ a := 100000000, b := -100000000, c := -193207021 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  simp only [Halfplane.contains, terminal7Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal7Triangle1Vertices : List QPoint :=
  [(6566177840862780170097253996201359783695202399/20679511040048114610299922706532981200000000000, 544439818638527893461531374249978102838486274247/144756577280336802272099458945730868400000000000), (46232789711265126441482792079765011968188633753/144756577280336802272099458945730868400000000000, 57404680543888201111218470372969093479231782399/20679511040048114610299922706532981200000000000), (116883001835610550096000629910633510750094429753/144756577280336802272099458945730868400000000000, 41869021065232662598850735375347050495742522399/20679511040048114610299922706532981200000000000)]
def terminal7Triangle1 : Polygon :=
  [ { a := -36467099964758234801938856961422492738536075600000000000, b := -68927291837805171769882878371599210297344000000000000, c := -11838308423889919385181273684467893242520480595598281607 },
    { a := -776782973932776925618386749881102149174463000000000000, b := -504644372316753026103698841649060705585041400000000000, c := -1648943980560308738589336169704040251374815155475539963 },
    { a := 18192765698435402990283139272952922462611561149399666186741572533104142769303408526800000000000, b := 5133050638786645164627020343247721015940575699674152672031928762098108316133627232000000000000, c := 25082353921393147592777269772653993594679730320284558239917895927815120765911119059770664373071 } ]
private theorem terminal7_leaf1 :
    Polygon.carrier ((⟨-terminal7Cut.a, -terminal7Cut.b, -terminal7Cut.c⟩ : Halfplane) :: terminal7Domain) ⊆ terminal7Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal7Triangle1, l.contains p
  intro l hl
  simp only [terminal7Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal7Cut.a, -terminal7Cut.b, -terminal7Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 25000000, b := 0, c := 13920417 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs2 : ({ a := 50000000, b := 50000000, c := 162069661 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs4 : ({ a := -100000000, b := 0, c := -49350663 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs5 : ({ a := -25000000, b := -25000000, c := -73879439 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs6 : ({ a := 0, b := -25000000, c := -61541773 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  have hs7 : ({ a := 100000000, b := -100000000, c := -193207021 } : Halfplane).contains p :=
    hp _ (by simp [terminal7Domain])
  simp only [Halfplane.contains, terminal7Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal7_cover_cert :
    PolygonCoverCert [terminal7Triangle0, terminal7Triangle1] terminal7Domain := by
  refine PolygonCoverCert.split terminal7Domain terminal7Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal7Triangle0 (by simp) terminal7_leaf0
  · exact PolygonCoverCert.leaf _ terminal7Triangle1 (by simp) terminal7_leaf1
theorem terminal7_polygon_cover :
    terminal7Domain.carrier ⊆ ⋃ K ∈ [terminal7Triangle0, terminal7Triangle1], Polygon.carrier K :=
  terminal7_cover_cert.sound

/-- Archived far15 terminal step 7, row 8; interval ['1/992', '9/7936']. -/
def terminal8Domain : Polygon :=
  [ { a := 3125000, b := 0, c := 1740143 },
    { a := 10000000, b := 10000000, c := 32415033 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -20000000, b := 0, c := -9872611 },
    { a := -100000000, b := -100000000, c := -295517809 },
    { a := 0, b := -100000000, c := -246154753 },
    { a := 100000000, b := -100000000, c := -193206361 } ]
def terminal8Cut : Halfplane := { a := -2028835219640993608658977012317017064214901600000000000, b := 3153908226948267916626767352771644688332164400000000000, c := 7241437517762742322796203157834361777028060056428479613 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal8Triangle0Vertices : List QPoint :=
  [(16345762640569110024708196055280321231674907129/38450984765179841630083025854938996400000000000, 98799089950719290421256098652800038794423335559/38450984765179841630083025854938996400000000000), (2499674605231619133878865796913581837375973/5866409504788561056292368253622000000000000, 12282239734670453973176178229403871535097/5913719258859436548681822836312500000000), (47884844910051789190975869582996768114996551129/38450984765179841630083025854938996400000000000, 119087442147129226507845868775970209436572351559/38450984765179841630083025854938996400000000000)]
def terminal8Triangle0 : Polygon :=
  [ { a := -111109821134620326670737733332950345606753731984404384753411552909915218947104400000000000, b := -224012846015527297219418561549547182869123567862912302273874842462598222259200000000000, c := -47809101375497624486789976243668195200176350860853190299337361645624592310179380728663011 },
    { a := 230129603296137454847573136442557262789927710324767369548701291022920954899104400000000000, b := -184797159151986042956071222090445895739458877186612985666905863012331396345740800000000000, c := -285748224746859631757349576604522291956907715746420813899944599835276174669773788831024989 },
    { a := -2028835219640993608658977012317017064214901600000000000, b := 3153908226948267916626767352771644688332164400000000000, c := 7241437517762742322796203157834361777028060056428479613 } ]
private theorem terminal8_leaf0 :
    Polygon.carrier (terminal8Cut :: terminal8Domain) ⊆ terminal8Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal8Triangle0, l.contains p
  intro l hl
  simp only [terminal8Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal8Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 3125000, b := 0, c := 1740143 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs2 : ({ a := 10000000, b := 10000000, c := 32415033 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs4 : ({ a := -20000000, b := 0, c := -9872611 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs5 : ({ a := -100000000, b := -100000000, c := -295517809 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs6 : ({ a := 0, b := -100000000, c := -246154753 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs7 : ({ a := 100000000, b := -100000000, c := -193206361 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  simp only [Halfplane.contains, terminal8Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs2 hs7 ⊢
    linarith only [hs2, hs7]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal8Triangle1Vertices : List QPoint :=
  [(12204229373082753087040098788599837794048819129/38450984765179841630083025854938996400000000000, 144612115200045301885149532802040184554157211559/38450984765179841630083025854938996400000000000), (12285373615836206730230673510568629389637056441/38450984765179841630083025854938996400000000000, 106732116861956207937491639021322817315160079129/38450984765179841630083025854938996400000000000), (31051845447986515980062164991156778289023172441/38450984765179841630083025854938996400000000000, 77845485801195109625245828637928836541240859129/38450984765179841630083025854938996400000000000)]
def terminal8Triangle1 : Polygon :=
  [ { a := -9686575734887658395535470731263688192292658000000000000, b := -20749997026559771175991044736566119529267200000000000, c := -3152530261812271647620402130711011435575650780518888487 },
    { a := -206333079005436416516041502738528434099423000000000000, b := -134046227372502208927367796289915349281329400000000000, c := -438010019055883144540863495675067636475379060488620379 },
    { a := 1283621324918798635284558372185190818242134226250393505100647404537170666826450626000000000000, b := 362354699278041635919426763306666891777014800001090809220405522435810832150148038400000000000, c := 1770214443360693307218495598725642311830512347355018568207451879781402541255955244546342983439 } ]
private theorem terminal8_leaf1 :
    Polygon.carrier ((⟨-terminal8Cut.a, -terminal8Cut.b, -terminal8Cut.c⟩ : Halfplane) :: terminal8Domain) ⊆ terminal8Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal8Triangle1, l.contains p
  intro l hl
  simp only [terminal8Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal8Cut.a, -terminal8Cut.b, -terminal8Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 3125000, b := 0, c := 1740143 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs2 : ({ a := 10000000, b := 10000000, c := 32415033 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs4 : ({ a := -20000000, b := 0, c := -9872611 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs5 : ({ a := -100000000, b := -100000000, c := -295517809 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs6 : ({ a := 0, b := -100000000, c := -246154753 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  have hs7 : ({ a := 100000000, b := -100000000, c := -193206361 } : Halfplane).contains p :=
    hp _ (by simp [terminal8Domain])
  simp only [Halfplane.contains, terminal8Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal8_cover_cert :
    PolygonCoverCert [terminal8Triangle0, terminal8Triangle1] terminal8Domain := by
  refine PolygonCoverCert.split terminal8Domain terminal8Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal8Triangle0 (by simp) terminal8_leaf0
  · exact PolygonCoverCert.leaf _ terminal8Triangle1 (by simp) terminal8_leaf1
theorem terminal8_polygon_cover :
    terminal8Domain.carrier ⊆ ⋃ K ∈ [terminal8Triangle0, terminal8Triangle1], Polygon.carrier K :=
  terminal8_cover_cert.sound

/-- Archived far15 terminal step 7, row 9; interval ['9/7936', '5/3968']. -/
def terminal9Domain : Polygon :=
  [ { a := 10000000, b := 0, c := 5568749 },
    { a := 50000000, b := 50000000, c := 162080671 },
    { a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 },
    { a := -25000000, b := 0, c := -12343861 },
    { a := 0, b := -25000000, c := -61535603 },
    { a := 50000000, b := -50000000, c := -96602847 } ]
def terminal9Cut : Halfplane := { a := -38189860650462156940621065153830054070326956000000000000, b := 59367717262328439373460192783891287498886854000000000000, c := 136306831430017608643745506374800672659938795278257042297 }
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 1, 12).
def terminal9Triangle0Vertices : List QPoint :=
  [(307595470475486054555220028431007292704541486149/723783644841844015292284482803433974000000000000, 1859658557117697452321271686259458447200135274043/723783644841844015292284482803433974000000000000), (9998707886425423832578828242623106589188473/23465644725733438246633436925326000000000000, 24563018085552579929418393769521909940033/11827441898051128148504756514781250000000), (901272643098770448289821956269920167693410026149/723783644841844015292284482803433974000000000000, 2241557163622319021727482337797758987903404834043/723783644841844015292284482803433974000000000000)]
def terminal9Triangle0 : Polygon :=
  [ { a := -8365918468071631559413339368222911362444581457828493690818682342162993612927290000000000000, b := -18975208323298930208671494998134736141938334993053894652749417756433121072128000000000000, c := -3604124042133583533653095884696477077326955211853617234472419387924136332561155049267519011 },
    { a := 5775805163187251474005970079860358804522508577242971536666892161988254163162430000000000000, b := -4637347468744204820119877083444162618026835402527294570733591772232259174322624000000000000, c := -7169689851798226972802806278912863996674455587792142117873875732074737645071841528800493663 },
    { a := -38189860650462156940621065153830054070326956000000000000, b := 59367717262328439373460192783891287498886854000000000000, c := 136306831430017608643745506374800672659938795278257042297 } ]
private theorem terminal9_leaf0 :
    Polygon.carrier (terminal9Cut :: terminal9Domain) ⊆ terminal9Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal9Triangle0, l.contains p
  intro l hl
  simp only [terminal9Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : terminal9Cut.contains p := hp _ (by simp)
  have hs1 : ({ a := 10000000, b := 0, c := 5568749 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs2 : ({ a := 50000000, b := 50000000, c := 162080671 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs4 : ({ a := -25000000, b := 0, c := -12343861 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs5 : ({ a := 0, b := -25000000, c := -61535603 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs6 : ({ a := 50000000, b := -50000000, c := -96602847 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  simp only [Halfplane.contains, terminal9Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
-- Branch 1: archived collision owner 13, Minkowski hull vertices (0, 2, 3).
def terminal9Triangle1Vertices : List QPoint :=
  [(229637153884085043937616936313249445356706406149/723783644841844015292284482803433974000000000000, 2722021864551535588689462440010696761058089934043/723783644841844015292284482803433974000000000000), (231344271977894782368286605127765249156676445957/723783644841844015292284482803433974000000000000, 2008986613038998676486763756537642545836415506149/723783644841844015292284482803433974000000000000), (584595702765587376110232459907826574027519505957/723783644841844015292284482803433974000000000000, 1465237961501399962232104289799234803508437806149/723783644841844015292284482803433974000000000000)]
def terminal9Triangle1 : Polygon :=
  [ { a := -7293423698223247027793786345215367648362456080000000000, b := -17461598896613217280293091752805278133698560000000000, c := -2379677858697255942861611071177665083227050126870495211 },
    { a := -3883918939554276530390424762417198159485555000000000000, b := -2523224505626375669585327534143295177648879000000000000, c := -8245069773981536540769971328436400886999498594927489919 },
    { a := 18192792682563717714199296954864878299305727420989644476527366735912637046788653415120000000000, b := 5138263845544512244542413182055933686732151215521823035344805437073925720920001539840000000000, c := 25096184192173987584605497127538127655819627455047020647575902228864632873118250134224927039679 } ]
private theorem terminal9_leaf1 :
    Polygon.carrier ((⟨-terminal9Cut.a, -terminal9Cut.b, -terminal9Cut.c⟩ : Halfplane) :: terminal9Domain) ⊆ terminal9Triangle1.carrier := by
  intro p hp
  change ∀ l ∈ terminal9Triangle1, l.contains p
  intro l hl
  simp only [terminal9Triangle1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : (⟨-terminal9Cut.a, -terminal9Cut.b, -terminal9Cut.c⟩ : Halfplane).contains p := hp _ (by simp)
  have hs1 : ({ a := 10000000, b := 0, c := 5568749 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs2 : ({ a := 50000000, b := 50000000, c := 162080671 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs3 : ({ a := 3926167468272503004794744600000000, b := 36091305889491574438877512800000000, c := 100955850775425819762136807590461413 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs4 : ({ a := -25000000, b := 0, c := -12343861 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs5 : ({ a := 0, b := -25000000, c := -61535603 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  have hs6 : ({ a := 50000000, b := -50000000, c := -96602847 } : Halfplane).contains p :=
    hp _ (by simp [terminal9Domain])
  simp only [Halfplane.contains, terminal9Cut] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs4 ⊢
    linarith only [hs0, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal9_cover_cert :
    PolygonCoverCert [terminal9Triangle0, terminal9Triangle1] terminal9Domain := by
  refine PolygonCoverCert.split terminal9Domain terminal9Cut ?_ ?_
  · exact PolygonCoverCert.leaf _ terminal9Triangle0 (by simp) terminal9_leaf0
  · exact PolygonCoverCert.leaf _ terminal9Triangle1 (by simp) terminal9_leaf1
theorem terminal9_polygon_cover :
    terminal9Domain.carrier ⊆ ⋃ K ∈ [terminal9Triangle0, terminal9Triangle1], Polygon.carrier K :=
  terminal9_cover_cert.sound

end
end ElevenSquare.Tasks.T07
