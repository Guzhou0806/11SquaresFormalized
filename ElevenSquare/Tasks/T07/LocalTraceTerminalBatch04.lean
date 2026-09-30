import ElevenSquare.Tasks.T07.LocalTraceCover
import Mathlib.Tactic.Linarith

/-! Generated exact polygon union certificates from far15y-self-300.json.
The emitter is untrusted; each closed split and arithmetic leaf is checked
inside Lean.  Triangle-to-semantic forbidden-center bridges are separate. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Archived far15 terminal step 7, row 220; interval ['233/256', '117/128']. -/
def terminal220Domain : Polygon :=
  [ { a := 5000000, b := 0, c := 2687581 },
    { a := 100000000, b := 100000000, c := 304059189 },
    { a := -100000000, b := 100000000, c := 197098369 },
    { a := -100000000, b := 0, c := -53480409 },
    { a := -6250000, b := -6250000, c := -18977787 },
    { a := 0, b := -100000000, c := -250162269 },
    { a := 2000000, b := -2000000, c := -3928213 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 3, 11).
def terminal220Triangle0Vertices : List QPoint :=
  [(687051663754506691828258921929452469203229/1788626084275777201083671957041520000000000, 2921793982253540444880714621170675833836899/1788626084275777201083671957041520000000000), (3268482441040118456967630019651350577906301/1788626084275777201083671957041520000000000, 1465170368442196405633816427472119909595229/1788626084275777201083671957041520000000000), (848374553614342958234287386891124346784099/1788626084275777201083671957041520000000000, 4672920903467763150260218881127347840060771/1788626084275777201083671957041520000000000)]
def terminal220Triangle0 : Polygon :=
  [ { a := -1302677495317508093472098887486875844015521127402835127711639155911352069200000000000, b := -2308607211502669837788317398003302180825479342469795540374334987812627774720000000000, c := -4271592294005182906399907040174231840584765579358216214322799504169161562322704303079 },
    { a := 320775053502556674462640245365522793046554200000000, b := 242010788742577549873334263276022623112220200000000, c := 784420331750811424836843816005599053110751858970497 },
    { a := -855335302509350863775820599232911196160000000000, b := 78797922142769364593741168067464163600000000000, c := -199833968132535411786588159902365482533053148187 } ]
private theorem terminal220_leaf0 :
    Polygon.carrier (terminal220Domain) ⊆ terminal220Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal220Triangle0, l.contains p
  intro l hl
  simp only [terminal220Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 5000000, b := 0, c := 2687581 } : Halfplane).contains p :=
    hp _ (by simp [terminal220Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 304059189 } : Halfplane).contains p :=
    hp _ (by simp [terminal220Domain])
  have hs2 : ({ a := -100000000, b := 100000000, c := 197098369 } : Halfplane).contains p :=
    hp _ (by simp [terminal220Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -53480409 } : Halfplane).contains p :=
    hp _ (by simp [terminal220Domain])
  have hs4 : ({ a := -6250000, b := -6250000, c := -18977787 } : Halfplane).contains p :=
    hp _ (by simp [terminal220Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -250162269 } : Halfplane).contains p :=
    hp _ (by simp [terminal220Domain])
  have hs6 : ({ a := 2000000, b := -2000000, c := -3928213 } : Halfplane).contains p :=
    hp _ (by simp [terminal220Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs5 ⊢
    linarith only [hs2, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs5 ⊢
    linarith only [hs1, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal220_cover_cert :
    PolygonCoverCert [terminal220Triangle0] terminal220Domain :=
  PolygonCoverCert.leaf _ terminal220Triangle0 (by simp) terminal220_leaf0
theorem terminal220_polygon_cover :
    terminal220Domain.carrier ⊆ ⋃ K ∈ [terminal220Triangle0], Polygon.carrier K :=
  terminal220_cover_cert.sound

/-- Archived far15 terminal step 7, row 221; interval ['117/128', '235/256']. -/
def terminal221Domain : Polygon :=
  [ { a := 25000000, b := 0, c := 13484741 },
    { a := 100000000, b := 100000000, c := 304224121 },
    { a := -50000000, b := 50000000, c := 98821811 },
    { a := -100000000, b := 0, c := -53290249 },
    { a := -20000000, b := -20000000, c := -60652993 },
    { a := 0, b := -100000000, c := -249937609 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 3, 11).
def terminal221Triangle0Vertices : List QPoint :=
  [(4348892591165163197016297595743307337141357/11266134643170671573152449482662000000000000, 18378060457361229740073262580365093277012499/11266134643170671573152449482662000000000000), (20613033475784426084812699503628419696407501/11266134643170671573152449482662000000000000, 9250079134539666963252977076577084097341357/11266134643170671573152449482662000000000000), (5318079581440179527127380663708050085332499/11266134643170671573152449482662000000000000, 29412312814982030599040816094540839271258643/11266134643170671573152449482662000000000000)]
def terminal221Triangle0 : Polygon :=
  [ { a := -2056741332065097236788128576944550193436005398184096789372122772103814800080000000000, b := -3664680021232351399921566128642771665842381156582128021596527558695431906560000000000, c := -6771999496233720926314040194299954367509703955007847597336331395472624331137439663071 },
    { a := 29220628522380237153315708721686601701329400000000, b := 22166599846875719648819302666551260305905800000000, c := 71663318628272621298503016340033876236737551863389 },
    { a := -216425150367622961881436111149812858880000000000, b := 19009574306114737558811591061085245840000000000, c := -52533601439589914488829943308550283152077652083 } ]
private theorem terminal221_leaf0 :
    Polygon.carrier (terminal221Domain) ⊆ terminal221Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal221Triangle0, l.contains p
  intro l hl
  simp only [terminal221Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 25000000, b := 0, c := 13484741 } : Halfplane).contains p :=
    hp _ (by simp [terminal221Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 304224121 } : Halfplane).contains p :=
    hp _ (by simp [terminal221Domain])
  have hs2 : ({ a := -50000000, b := 50000000, c := 98821811 } : Halfplane).contains p :=
    hp _ (by simp [terminal221Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -53290249 } : Halfplane).contains p :=
    hp _ (by simp [terminal221Domain])
  have hs4 : ({ a := -20000000, b := -20000000, c := -60652993 } : Halfplane).contains p :=
    hp _ (by simp [terminal221Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -249937609 } : Halfplane).contains p :=
    hp _ (by simp [terminal221Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs5 ⊢
    linarith only [hs2, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal221_cover_cert :
    PolygonCoverCert [terminal221Triangle0] terminal221Domain :=
  PolygonCoverCert.leaf _ terminal221Triangle0 (by simp) terminal221_leaf0
theorem terminal221_polygon_cover :
    terminal221Domain.carrier ⊆ ⋃ K ∈ [terminal221Triangle0], Polygon.carrier K :=
  terminal221_cover_cert.sound

/-- Archived far15 terminal step 7, row 222; interval ['235/256', '59/64']. -/
def terminal222Domain : Polygon :=
  [ { a := 10000000, b := 0, c := 5412541 },
    { a := 25000000, b := 25000000, c := 76097801 },
    { a := -100000000, b := 100000000, c := 198191461 },
    { a := -100000000, b := 0, c := -53099871 },
    { a := -50000000, b := -50000000, c := -151442453 },
    { a := 0, b := -20000000, c := -49943273 },
    { a := 25000000, b := -25000000, c := -48897739 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 3, 11).
def terminal222Triangle0Vertices : List QPoint :=
  [(17617380987615209226105115095013284231089637/45416282090834265654068444421814000000000000, 10569066515701319164532267774456698253873613/6488040298690609379152634917402000000000000), (11885466182576818895630102542744291102946387/6488040298690609379152634917402000000000000, 37375148641193684736880654357790423530489637/45416282090834265654068444421814000000000000), (3047970336146205035603431057279935068593613/6488040298690609379152634917402000000000000, 118481509804680071157763614980636770303710363/45416282090834265654068444421814000000000000)]
def terminal222Triangle0 : Polygon :=
  [ { a := -1445751000279878398864517703085954967204480152324188762080102671294373579440000000000, b := -2589947695537066512593650041899773881673269312743895461445134089480621617920000000000, c := -4779864014742800721700751495710139228981862278943389841646651022358391760339229382377 },
    { a := 8110636116348638642088296062284634677322072600000000, b := 6186247092501429702018670039825049224046941800000000, c := 19948853183571681939445673726561833428737466282252521 },
    { a := -876178180701509186480793080736743178240000000000, b := 73216496684275736346236820621294785680000000000, c := -220607108214983760262815740559511554788415148419 } ]
private theorem terminal222_leaf0 :
    Polygon.carrier (terminal222Domain) ⊆ terminal222Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal222Triangle0, l.contains p
  intro l hl
  simp only [terminal222Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 10000000, b := 0, c := 5412541 } : Halfplane).contains p :=
    hp _ (by simp [terminal222Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 76097801 } : Halfplane).contains p :=
    hp _ (by simp [terminal222Domain])
  have hs2 : ({ a := -100000000, b := 100000000, c := 198191461 } : Halfplane).contains p :=
    hp _ (by simp [terminal222Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -53099871 } : Halfplane).contains p :=
    hp _ (by simp [terminal222Domain])
  have hs4 : ({ a := -50000000, b := -50000000, c := -151442453 } : Halfplane).contains p :=
    hp _ (by simp [terminal222Domain])
  have hs5 : ({ a := 0, b := -20000000, c := -49943273 } : Halfplane).contains p :=
    hp _ (by simp [terminal222Domain])
  have hs6 : ({ a := 25000000, b := -25000000, c := -48897739 } : Halfplane).contains p :=
    hp _ (by simp [terminal222Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal222_cover_cert :
    PolygonCoverCert [terminal222Triangle0] terminal222Domain :=
  PolygonCoverCert.leaf _ terminal222Triangle0 (by simp) terminal222_leaf0
theorem terminal222_polygon_cover :
    terminal222Domain.carrier ⊆ ⋃ K ∈ [terminal222Triangle0], Polygon.carrier K :=
  terminal222_cover_cert.sound

/-- Archived far15 terminal step 7, row 223; interval ['59/64', '237/256']. -/
def terminal223Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 54310897 },
    { a := 25000000, b := 25000000, c := 76140101 },
    { a := -12500000, b := 0, c := -6613661 },
    { a := -100000000, b := -100000000, c := -302504439 },
    { a := 0, b := -50000000, c := -124749299 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 3, 11).
def terminal223Triangle0Vertices : List QPoint :=
  [(1115108964512230957208212629580323214606629/2860681258508770316393487398198000000000000, 4653658994181581463175214962304342398851419/2860681258508770316393487398198000000000000), (5246905413764581309900315623810329240328581/2860681258508770316393487398198000000000000, 2359611443238236720218117846178926360406629/2860681258508770316393487398198000000000000), (1337486792132005256311288434783729200131419/2860681258508770316393487398198000000000000, 7457489413634735734141581548322306628993371/2860681258508770316393487398198000000000000)]
def terminal223Triangle0 : Polygon :=
  [ { a := -3281269417555784912162672811660119448127692031609921492240790379684244210000000000000, b := -5909876333174641076577797483790687576352981810072344062310012578526921248000000000000, c := -10893042348632487495578338534624104780772670023097195573680427502570596576837919581399 },
    { a := 509787797039649901392346370214338026858674200000000, b := 390941862163257605358902718902660004019716200000000, c := 1257490408293496415385091924652049750210558522701097 },
    { a := -1385576688921239920285818408291997696000000000000, b := 109893070545614411704255818401776170000000000000, c := -361334946917942636677836320785567396389272708523 } ]
private theorem terminal223_leaf0 :
    Polygon.carrier (terminal223Domain) ⊆ terminal223Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal223Triangle0, l.contains p
  intro l hl
  simp only [terminal223Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 54310897 } : Halfplane).contains p :=
    hp _ (by simp [terminal223Domain])
  have hs1 : ({ a := 25000000, b := 25000000, c := 76140101 } : Halfplane).contains p :=
    hp _ (by simp [terminal223Domain])
  have hs2 : ({ a := -12500000, b := 0, c := -6613661 } : Halfplane).contains p :=
    hp _ (by simp [terminal223Domain])
  have hs3 : ({ a := -100000000, b := -100000000, c := -302504439 } : Halfplane).contains p :=
    hp _ (by simp [terminal223Domain])
  have hs4 : ({ a := 0, b := -50000000, c := -124749299 } : Halfplane).contains p :=
    hp _ (by simp [terminal223Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs0 hs3 ⊢
    linarith only [hs0, hs3]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs1 ⊢
    linarith only [hs0, hs1]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal223_cover_cert :
    PolygonCoverCert [terminal223Triangle0] terminal223Domain :=
  PolygonCoverCert.leaf _ terminal223Triangle0 (by simp) terminal223_leaf0
theorem terminal223_polygon_cover :
    terminal223Domain.carrier ⊆ ⋃ K ∈ [terminal223Triangle0], Polygon.carrier K :=
  terminal223_cover_cert.sound

/-- Archived far15 terminal step 7, row 224; interval ['237/256', '119/128']. -/
def terminal224Domain : Polygon :=
  [ { a := 100000000, b := 0, c := 54495441 },
    { a := 100000000, b := 100000000, c := 304731689 },
    { a := 0, b := 100000000, c := 252013177 },
    { a := -100000000, b := 0, c := -52718511 },
    { a := -25000000, b := -25000000, c := -75530897 },
    { a := 0, b := -100000000, c := -249284261 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal224Triangle0Vertices : List QPoint :=
  [(3613735554586848038469854868243205092585049/9225682051566405279311590390938800000000000, 14987499969523686359590831720139282913203751/9225682051566405279311590390938800000000000), (24341839643805855986165559737341113041764249/9225682051566405279311590390938800000000000, 12372254806714854424707835601122054979837049/9225682051566405279311590390938800000000000), (4292862014542158763586753901375793221171751/9225682051566405279311590390938800000000000, 24032849243114505842513685295420393177574951/9225682051566405279311590390938800000000000)]
def terminal224Triangle0 : Polygon :=
  [ { a := -1340412242165072344046371123263434575036914201190676860034992015168802213200000000000, b := -10623938769939333989852023464773753702926124088644122578565264616143190720000000000000, c := -17784070213014290343567361129655992585976695894325110039293133200985264866244313934311 },
    { a := 1166059443639965141780584969429833819773790200000000, b := 2004897762926369722257880583596531982059249800000000, c := 5765333953551574065532646726304314263785087599404873 },
    { a := -4487371749881899527857157566152632320000000000000, b := 336912682841153554395179969486694037200000000000, c := -1210392462364007383745839824325728484326080050831 } ]
private theorem terminal224_leaf0 :
    Polygon.carrier (terminal224Domain) ⊆ terminal224Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal224Triangle0, l.contains p
  intro l hl
  simp only [terminal224Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 100000000, b := 0, c := 54495441 } : Halfplane).contains p :=
    hp _ (by simp [terminal224Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 304731689 } : Halfplane).contains p :=
    hp _ (by simp [terminal224Domain])
  have hs2 : ({ a := 0, b := 100000000, c := 252013177 } : Halfplane).contains p :=
    hp _ (by simp [terminal224Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -52718511 } : Halfplane).contains p :=
    hp _ (by simp [terminal224Domain])
  have hs4 : ({ a := -25000000, b := -25000000, c := -75530897 } : Halfplane).contains p :=
    hp _ (by simp [terminal224Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -249284261 } : Halfplane).contains p :=
    hp _ (by simp [terminal224Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs4 hs5 ⊢
    linarith only [hs4, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs2 ⊢
    linarith only [hs0, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal224_cover_cert :
    PolygonCoverCert [terminal224Triangle0] terminal224Domain :=
  PolygonCoverCert.leaf _ terminal224Triangle0 (by simp) terminal224_leaf0
theorem terminal224_polygon_cover :
    terminal224Domain.carrier ⊆ ⋃ K ∈ [terminal224Triangle0], Polygon.carrier K :=
  terminal224_cover_cert.sound

/-- Archived far15 terminal step 7, row 225; interval ['119/128', '239/256']. -/
def terminal225Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 27339527 },
    { a := 4000000, b := 4000000, c := 12196201 },
    { a := -100000000, b := 100000000, c := 199849921 },
    { a := -100000000, b := 0, c := -52527551 },
    { a := -12500000, b := -12500000, c := -37717797 },
    { a := 0, b := -100000000, c := -249073309 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal225Triangle0Vertices : List QPoint :=
  [(914910209471287171243201152836571013785777/2324441503979026823227951477636400000000000, 3771017833862269135977387858436059854534607/2324441503979026823227951477636400000000000), (6138141056540623067130664421456080295569393/2324441503979026823227951477636400000000000, 3121648480880612177627725973630086323341777/2324441503979026823227951477636400000000000), (1076467968211123199270622168835536013638607/2324441503979026823227951477636400000000000, 6050739461507955347675719229883769120694223/2324441503979026823227951477636400000000000)]
def terminal225Triangle0 : Polygon :=
  [ { a := -754710537741285123223959181906542245115261391537574051813961362780513506000000000000, b := -6070547282895746689120520305731633584714451752893159930939604084263962611200000000000, c := -10145505662719337093380158827482179103441554114187583792227670489393061403007727988911 },
    { a := 292909098062734317004799325625368279735244600000000, b := 506167308832949986786004225262054428193078600000000, c := 1453249636766698452300631826805806043338788294215713 },
    { a := -1135368803735547693752046443348544307200000000000, b := 80460542660234013486035540398383986000000000000, c := -316352279676688830077541835980953226676919782791 } ]
private theorem terminal225_leaf0 :
    Polygon.carrier (terminal225Domain) ⊆ terminal225Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal225Triangle0, l.contains p
  intro l hl
  simp only [terminal225Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 27339527 } : Halfplane).contains p :=
    hp _ (by simp [terminal225Domain])
  have hs1 : ({ a := 4000000, b := 4000000, c := 12196201 } : Halfplane).contains p :=
    hp _ (by simp [terminal225Domain])
  have hs2 : ({ a := -100000000, b := 100000000, c := 199849921 } : Halfplane).contains p :=
    hp _ (by simp [terminal225Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -52527551 } : Halfplane).contains p :=
    hp _ (by simp [terminal225Domain])
  have hs4 : ({ a := -12500000, b := -12500000, c := -37717797 } : Halfplane).contains p :=
    hp _ (by simp [terminal225Domain])
  have hs5 : ({ a := 0, b := -100000000, c := -249073309 } : Halfplane).contains p :=
    hp _ (by simp [terminal225Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs5 ⊢
    linarith only [hs2, hs5]
  · simp only [Halfplane.contains]
    norm_num at hs0 hs2 ⊢
    linarith only [hs0, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs3 ⊢
    linarith only [hs1, hs3]
theorem terminal225_cover_cert :
    PolygonCoverCert [terminal225Triangle0] terminal225Domain :=
  PolygonCoverCert.leaf _ terminal225Triangle0 (by simp) terminal225_leaf0
theorem terminal225_polygon_cover :
    terminal225Domain.carrier ⊆ ⋃ K ∈ [terminal225Triangle0], Polygon.carrier K :=
  terminal225_cover_cert.sound

/-- Archived far15 terminal step 7, row 226; interval ['239/256', '15/16']. -/
def terminal226Domain : Polygon :=
  [ { a := 25000000, b := 0, c := 13715437 },
    { a := 5000000, b := 5000000, c := 15254019 },
    { a := 0, b := 50000000, c := 126371979 },
    { a := -100000000, b := 0, c := -52336421 },
    { a := -12500000, b := -12500000, c := -37670103 },
    { a := 0, b := -20000000, c := -49773139 },
    { a := 25000000, b := -25000000, c := -48500987 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal226Triangle0Vertices : List QPoint :=
  [(1090020174489875000687118088956198192911949/2756010429382178058967128691174000000000000, 4465125750529081054582074824753679872469043/2756010429382178058967128691174000000000000), (7283823492377706598275517609926418235170957/2756010429382178058967128691174000000000000, 3706473924997237539024935901498195208371949/2756010429382178058967128691174000000000000), (1270290552692280271760006295893828545109043/2756010429382178058967128691174000000000000, 7168911318420925100699170319053283493888051/2756010429382178058967128691174000000000000)]
def terminal226Triangle0 : Polygon :=
  [ { a := -41817046868711785651702546738256882461745995472538084455374070973536967120000000000, b := -341403730832816037296077867344558797645195320445179901730944027547031907840000000000, c := -569661129673133974885594161788238603368153854896759896881744500544883744775219933311 },
    { a := 69248747868473751233484688351101765710322040000000, b := 120270658793708526530310226280651793801238280000000, c := 344764920761295319767802992024499493125986662695833 },
    { a := -54072483662809632368445630180243292160000000000, b := 3605192362883414762496080383498532880000000000, c := -15545101123481327624361243246669591838447368939 } ]
private theorem terminal226_leaf0 :
    Polygon.carrier (terminal226Domain) ⊆ terminal226Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal226Triangle0, l.contains p
  intro l hl
  simp only [terminal226Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 25000000, b := 0, c := 13715437 } : Halfplane).contains p :=
    hp _ (by simp [terminal226Domain])
  have hs1 : ({ a := 5000000, b := 5000000, c := 15254019 } : Halfplane).contains p :=
    hp _ (by simp [terminal226Domain])
  have hs2 : ({ a := 0, b := 50000000, c := 126371979 } : Halfplane).contains p :=
    hp _ (by simp [terminal226Domain])
  have hs3 : ({ a := -100000000, b := 0, c := -52336421 } : Halfplane).contains p :=
    hp _ (by simp [terminal226Domain])
  have hs4 : ({ a := -12500000, b := -12500000, c := -37670103 } : Halfplane).contains p :=
    hp _ (by simp [terminal226Domain])
  have hs5 : ({ a := 0, b := -20000000, c := -49773139 } : Halfplane).contains p :=
    hp _ (by simp [terminal226Domain])
  have hs6 : ({ a := 25000000, b := -25000000, c := -48500987 } : Halfplane).contains p :=
    hp _ (by simp [terminal226Domain])
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
theorem terminal226_cover_cert :
    PolygonCoverCert [terminal226Triangle0] terminal226Domain :=
  PolygonCoverCert.leaf _ terminal226Triangle0 (by simp) terminal226_leaf0
theorem terminal226_polygon_cover :
    terminal226Domain.carrier ⊆ ⋃ K ∈ [terminal226Triangle0], Polygon.carrier K :=
  terminal226_cover_cert.sound

/-- Archived far15 terminal step 7, row 227; interval ['15/16', '241/256']. -/
def terminal227Domain : Polygon :=
  [ { a := 20000000, b := 0, c := 11008707 },
    { a := 100000000, b := 100000000, c := 305257723 },
    { a := -25000000, b := 0, c := -13036283 },
    { a := -100000000, b := -100000000, c := -300978957 },
    { a := 0, b := -100000000, c := -248661377 },
    { a := 100000000, b := -100000000, c := -193617843 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal227Triangle0Vertices : List QPoint :=
  [(73301228489691700713693965369962208328797/184447147227080760448377403654000000000000, 298429166305019912192379108830720546023971/184447147227080760448377403654000000000000), (487874161021547116069039854740747254416029/184447147227080760448377403654000000000000, 248408486788733855008287188275879842988797/184447147227080760448377403654000000000000), (84613488461680219410682574495777711463971/184447147227080760448377403654000000000000, 479431205600836205376589793080653014471203/184447147227080760448377403654000000000000)]
def terminal227Triangle0 : Polygon :=
  [ { a := -61507810927593581507916141235861605818190954151983521338075703720838640000000000, b := -509778631487105031729607516903231902043979995162811890270945438396971520000000000, c := -849248212576945367528933524569874446244570282694083853891799452720859015656514293 },
    { a := 23102271881210235036830260480477317148240600000000, b := 40326067255986689665835728024496954295205800000000, c := 115417013366590602526930541589230719909897471508237 },
    { a := -3633933427352610642971423996214231040000000000, b := 227113461323649081955296064667243280000000000, c := -1076701410354371243172306974881863814833723611 } ]
private theorem terminal227_leaf0 :
    Polygon.carrier (terminal227Domain) ⊆ terminal227Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal227Triangle0, l.contains p
  intro l hl
  simp only [terminal227Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 20000000, b := 0, c := 11008707 } : Halfplane).contains p :=
    hp _ (by simp [terminal227Domain])
  have hs1 : ({ a := 100000000, b := 100000000, c := 305257723 } : Halfplane).contains p :=
    hp _ (by simp [terminal227Domain])
  have hs2 : ({ a := -25000000, b := 0, c := -13036283 } : Halfplane).contains p :=
    hp _ (by simp [terminal227Domain])
  have hs3 : ({ a := -100000000, b := -100000000, c := -300978957 } : Halfplane).contains p :=
    hp _ (by simp [terminal227Domain])
  have hs4 : ({ a := 0, b := -100000000, c := -248661377 } : Halfplane).contains p :=
    hp _ (by simp [terminal227Domain])
  have hs5 : ({ a := 100000000, b := -100000000, c := -193617843 } : Halfplane).contains p :=
    hp _ (by simp [terminal227Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal227_cover_cert :
    PolygonCoverCert [terminal227Triangle0] terminal227Domain :=
  PolygonCoverCert.leaf _ terminal227Triangle0 (by simp) terminal227_leaf0
theorem terminal227_polygon_cover :
    terminal227Domain.carrier ⊆ ⋃ K ∈ [terminal227Triangle0], Polygon.carrier K :=
  terminal227_cover_cert.sound

/-- Archived far15 terminal step 7, row 228; interval ['241/256', '121/128']. -/
def terminal228Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 27612213 },
    { a := 50000000, b := 50000000, c := 152718511 },
    { a := -50000000, b := 0, c := -25976847 },
    { a := -25000000, b := -25000000, c := -75149199 },
    { a := 0, b := -100000000, c := -248460311 },
    { a := 50000000, b := -50000000, c := -96617943 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal228Triangle0Vertices : List QPoint :=
  [(240538471712766524037259006145787098000811/602376267069350140184905484842000000000000, 973323629389223796756996926275899962650581/602376267069350140184905484842000000000000), (1594623179330216402946160707072353735469419/602376267069350140184905484842000000000000, 812412085247509896610091993121690927180811/602376267069350140184905484842000000000000), (275034218051212525467200332175907055770581/602376267069350140184905484842000000000000, 1564601403536674316224594927450361586399189/602376267069350140184905484842000000000000)]
def terminal228Triangle0 : Polygon :=
  [ { a := -48464647644225288148050405569324672634199956919122068662177498542113170000000000000, b := -407834245735145943206126572299276706464931300856829247572337302897419968000000000000, c := -678334029513725740875407627733979600073712003476245695264212794986748135759543222359 },
    { a := 271548490357099068452889145967029118851400000000, b := 476385906598918367320924323067309270649400000000, c := 1361340460486139192001334015776790625049843664207 },
    { a := -297930482682364024534332773558974464000000000000, b := 17381567186286098295035447765115910000000000000, c := -90883150475334568001212860059966038952134599357 } ]
private theorem terminal228_leaf0 :
    Polygon.carrier (terminal228Domain) ⊆ terminal228Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal228Triangle0, l.contains p
  intro l hl
  simp only [terminal228Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 27612213 } : Halfplane).contains p :=
    hp _ (by simp [terminal228Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 152718511 } : Halfplane).contains p :=
    hp _ (by simp [terminal228Domain])
  have hs2 : ({ a := -50000000, b := 0, c := -25976847 } : Halfplane).contains p :=
    hp _ (by simp [terminal228Domain])
  have hs3 : ({ a := -25000000, b := -25000000, c := -75149199 } : Halfplane).contains p :=
    hp _ (by simp [terminal228Domain])
  have hs4 : ({ a := 0, b := -100000000, c := -248460311 } : Halfplane).contains p :=
    hp _ (by simp [terminal228Domain])
  have hs5 : ({ a := 50000000, b := -50000000, c := -96617943 } : Halfplane).contains p :=
    hp _ (by simp [terminal228Domain])
  simp only [Halfplane.contains] at hs0 hs1 hs2 hs3 hs4 hs5
  rcases hl with rfl | rfl | rfl
  · simp only [Halfplane.contains]
    norm_num at hs2 hs4 ⊢
    linarith only [hs2, hs4]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
  · simp only [Halfplane.contains]
    norm_num at hs1 hs2 ⊢
    linarith only [hs1, hs2]
theorem terminal228_cover_cert :
    PolygonCoverCert [terminal228Triangle0] terminal228Domain :=
  PolygonCoverCert.leaf _ terminal228Triangle0 (by simp) terminal228_leaf0
theorem terminal228_polygon_cover :
    terminal228Domain.carrier ⊆ ⋃ K ∈ [terminal228Triangle0], Polygon.carrier K :=
  terminal228_cover_cert.sound

/-- Archived far15 terminal step 7, row 229; interval ['121/128', '243/256']. -/
def terminal229Domain : Polygon :=
  [ { a := 50000000, b := 0, c := 27673641 },
    { a := 50000000, b := 50000000, c := 152809123 },
    { a := -12500000, b := 12500000, c := 25261751 },
    { a := -50000000, b := 0, c := -25881059 },
    { a := -50000000, b := -50000000, c := -150107181 },
    { a := 0, b := -50000000, c := -124134901 },
    { a := 5000000, b := -5000000, c := -9650147 } ]
-- Branch 0: archived collision owner 9, Minkowski hull vertices (0, 4, 11).
def terminal229Triangle0Vertices : List QPoint :=
  [(192426378820162963524999902605952672679789/479599614459661727233661948489840000000000, 110558945598896745693844800339359849797013/68514230637094532461951706927120000000000), (181519128413502795645129716265507699766187/68514230637094532461951706927120000000000, 647740406886511763347768191941103461733389/479599614459661727233661948489840000000000), (31135561253733865654670519179383661560213/68514230637094532461951706927120000000000, 1244788922551799307085005837842043573608211/479599614459661727233661948489840000000000)]
def terminal229Triangle0 : Polygon :=
  [ { a := -30256072188683849976840186541396667568060173655937000296141593411997333840000000000, b := -258553955467584705262645806803414207043074395122076755157706549542887718400000000000, c := -429358633907641195471931435644128440237772270220745116341776406185972477861176098599 },
    { a := 59704851566528754373723764590094011187482200000000, b := 105268497011838250993321437960286826744181800000000, c := 300354010038080241241163690395524394126263893250333 },
    { a := -238188352525246400213325870097994137600000000000, b := 12910342021639634035402945991398002960000000000, c := -74733682981208823723727694367873740782889858331 } ]
private theorem terminal229_leaf0 :
    Polygon.carrier (terminal229Domain) ⊆ terminal229Triangle0.carrier := by
  intro p hp
  change ∀ l ∈ terminal229Triangle0, l.contains p
  intro l hl
  simp only [terminal229Triangle0, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  have hs0 : ({ a := 50000000, b := 0, c := 27673641 } : Halfplane).contains p :=
    hp _ (by simp [terminal229Domain])
  have hs1 : ({ a := 50000000, b := 50000000, c := 152809123 } : Halfplane).contains p :=
    hp _ (by simp [terminal229Domain])
  have hs2 : ({ a := -12500000, b := 12500000, c := 25261751 } : Halfplane).contains p :=
    hp _ (by simp [terminal229Domain])
  have hs3 : ({ a := -50000000, b := 0, c := -25881059 } : Halfplane).contains p :=
    hp _ (by simp [terminal229Domain])
  have hs4 : ({ a := -50000000, b := -50000000, c := -150107181 } : Halfplane).contains p :=
    hp _ (by simp [terminal229Domain])
  have hs5 : ({ a := 0, b := -50000000, c := -124134901 } : Halfplane).contains p :=
    hp _ (by simp [terminal229Domain])
  have hs6 : ({ a := 5000000, b := -5000000, c := -9650147 } : Halfplane).contains p :=
    hp _ (by simp [terminal229Domain])
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
theorem terminal229_cover_cert :
    PolygonCoverCert [terminal229Triangle0] terminal229Domain :=
  PolygonCoverCert.leaf _ terminal229Triangle0 (by simp) terminal229_leaf0
theorem terminal229_polygon_cover :
    terminal229Domain.carrier ⊆ ⋃ K ∈ [terminal229Triangle0], Polygon.carrier K :=
  terminal229_cover_cert.sound

end
end ElevenSquare.Tasks.T07
