import ElevenSquare.Tasks.T04.Completeness.Support

/-! Memoized exact original halfplanes for view 1. Each lookup identity is kernel-checked by reflexivity. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxRecDepth 10000

def plane_1_0_5 : IntegerPlane := ⟨(-2145688000000), (-699324000000), (-1695048727641)⟩
theorem plane_1_0_5_eq : sourcePlane 1 0 5 = plane_1_0_5 := by rfl
theorem plane_1_0_5_sound (p : Point) (h : ClosedCell 0 (view 1 p)) :
    plane_1_0_5.rational.contains p := by
  rw [← plane_1_0_5_eq]
  exact sourcePlane_sound 1 0 5 p h

def plane_1_0_6 : IntegerPlane := ⟨(-4229044000000), 46700000000, (-2660888019700)⟩
theorem plane_1_0_6_eq : sourcePlane 1 0 6 = plane_1_0_6 := by rfl
theorem plane_1_0_6_sound (p : Point) (h : ClosedCell 0 (view 1 p)) :
    plane_1_0_6.rational.contains p := by
  rw [← plane_1_0_6_eq]
  exact sourcePlane_sound 1 0 6 p h

def plane_1_0_8 : IntegerPlane := ⟨15204000000, 2139684000000, 584166228432⟩
theorem plane_1_0_8_eq : sourcePlane 1 0 8 = plane_1_0_8 := by rfl
theorem plane_1_0_8_sound (p : Point) (h : ClosedCell 0 (view 1 p)) :
    plane_1_0_8.rational.contains p := by
  rw [← plane_1_0_8_eq]
  exact sourcePlane_sound 1 0 8 p h

def plane_1_0_9 : IntegerPlane := ⟨(-2129316000000), 1440116000000, (-1301343880216)⟩
theorem plane_1_0_9_eq : sourcePlane 1 0 9 = plane_1_0_9 := by rfl
theorem plane_1_0_9_sound (p : Point) (h : ClosedCell 0 (view 1 p)) :
    plane_1_0_9.rational.contains p := by
  rw [← plane_1_0_9_eq]
  exact sourcePlane_sound 1 0 9 p h

def plane_1_1_4 : IntegerPlane := ⟨2145688000000, 699324000000, 1695048727641⟩
theorem plane_1_1_4_eq : sourcePlane 1 1 4 = plane_1_1_4 := by rfl
theorem plane_1_1_4_sound (p : Point) (h : ClosedCell 1 (view 1 p)) :
    plane_1_1_4.rational.contains p := by
  rw [← plane_1_1_4_eq]
  exact sourcePlane_sound 1 1 4 p h

def plane_1_1_6 : IntegerPlane := ⟨(-2083356000000), 746024000000, (-965839292059)⟩
theorem plane_1_1_6_eq : sourcePlane 1 1 6 = plane_1_1_6 := by rfl
theorem plane_1_1_6_sound (p : Point) (h : ClosedCell 1 (view 1 p)) :
    plane_1_1_6.rational.contains p := by
  rw [← plane_1_1_6_eq]
  exact sourcePlane_sound 1 1 6 p h

def plane_1_1_7 : IntegerPlane := ⟨(-3938876000000), 458408000000, (-1465215532459)⟩
theorem plane_1_1_7_eq : sourcePlane 1 1 7 = plane_1_1_7 := by rfl
theorem plane_1_1_7_sound (p : Point) (h : ClosedCell 1 (view 1 p)) :
    plane_1_1_7.rational.contains p := by
  rw [← plane_1_1_7_eq]
  exact sourcePlane_sound 1 1 7 p h

def plane_1_1_9 : IntegerPlane := ⟨16372000000, 2139440000000, 393704847425⟩
theorem plane_1_1_9_eq : sourcePlane 1 1 9 = plane_1_1_9 := by rfl
theorem plane_1_1_9_sound (p : Point) (h : ClosedCell 1 (view 1 p)) :
    plane_1_1_9.rational.contains p := by
  rw [← plane_1_1_9_eq]
  exact sourcePlane_sound 1 1 9 p h

def plane_1_1_15 : IntegerPlane := ⟨(-4189660000000), 4432944000000, (-99093043927)⟩
theorem plane_1_1_15_eq : sourcePlane 1 1 15 = plane_1_1_15 := by rfl
theorem plane_1_1_15_sound (p : Point) (h : ClosedCell 1 (view 1 p)) :
    plane_1_1_15.rational.contains p := by
  rw [← plane_1_1_15_eq]
  exact sourcePlane_sound 1 1 15 p h

def plane_1_2_4 : IntegerPlane := ⟨4229044000000, (-46700000000), 2660888019700⟩
theorem plane_1_2_4_eq : sourcePlane 1 2 4 = plane_1_2_4 := by rfl
theorem plane_1_2_4_sound (p : Point) (h : ClosedCell 2 (view 1 p)) :
    plane_1_2_4.rational.contains p := by
  rw [← plane_1_2_4_eq]
  exact sourcePlane_sound 1 2 4 p h

def plane_1_2_5 : IntegerPlane := ⟨2083356000000, (-746024000000), 965839292059⟩
theorem plane_1_2_5_eq : sourcePlane 1 2 5 = plane_1_2_5 := by rfl
theorem plane_1_2_5_sound (p : Point) (h : ClosedCell 2 (view 1 p)) :
    plane_1_2_5.rational.contains p := by
  rw [← plane_1_2_5_eq]
  exact sourcePlane_sound 1 2 5 p h

def plane_1_2_7 : IntegerPlane := ⟨(-1855520000000), (-287616000000), (-499376240400)⟩
theorem plane_1_2_7_eq : sourcePlane 1 2 7 = plane_1_2_7 := by rfl
theorem plane_1_2_7_sound (p : Point) (h : ClosedCell 2 (view 1 p)) :
    plane_1_2_7.rational.contains p := by
  rw [← plane_1_2_7_eq]
  exact sourcePlane_sound 1 2 7 p h

def plane_1_2_9 : IntegerPlane := ⟨2099728000000, 1393416000000, 1359544139484⟩
theorem plane_1_2_9_eq : sourcePlane 1 2 9 = plane_1_2_9 := by rfl
theorem plane_1_2_9_sound (p : Point) (h : ClosedCell 2 (view 1 p)) :
    plane_1_2_9.rational.contains p := by
  rw [← plane_1_2_9_eq]
  exact sourcePlane_sound 1 2 9 p h

def plane_1_2_10 : IntegerPlane := ⟨(-13084000000), 2218132000000, 610502975028⟩
theorem plane_1_2_10_eq : sourcePlane 1 2 10 = plane_1_2_10 := by rfl
theorem plane_1_2_10_sound (p : Point) (h : ClosedCell 2 (view 1 p)) :
    plane_1_2_10.rational.contains p := by
  rw [← plane_1_2_10_eq]
  exact sourcePlane_sound 1 2 10 p h

def plane_1_2_11 : IntegerPlane := ⟨(-2058052000000), 1574160000000, (-116004500953)⟩
theorem plane_1_2_11_eq : sourcePlane 1 2 11 = plane_1_2_11 := by rfl
theorem plane_1_2_11_sound (p : Point) (h : ClosedCell 2 (view 1 p)) :
    plane_1_2_11.rational.contains p := by
  rw [← plane_1_2_11_eq]
  exact sourcePlane_sound 1 2 11 p h

def plane_1_3_4 : IntegerPlane := ⟨6084564000000, 240916000000, 3160264260100⟩
theorem plane_1_3_4_eq : sourcePlane 1 3 4 = plane_1_3_4 := by rfl
theorem plane_1_3_4_sound (p : Point) (h : ClosedCell 3 (view 1 p)) :
    plane_1_3_4.rational.contains p := by
  rw [← plane_1_3_4_eq]
  exact sourcePlane_sound 1 3 4 p h

def plane_1_3_5 : IntegerPlane := ⟨3938876000000, (-458408000000), 1465215532459⟩
theorem plane_1_3_5_eq : sourcePlane 1 3 5 = plane_1_3_5 := by rfl
theorem plane_1_3_5_sound (p : Point) (h : ClosedCell 3 (view 1 p)) :
    plane_1_3_5.rational.contains p := by
  rw [← plane_1_3_5_eq]
  exact sourcePlane_sound 1 3 5 p h

def plane_1_3_6 : IntegerPlane := ⟨1855520000000, 287616000000, 499376240400⟩
theorem plane_1_3_6_eq : sourcePlane 1 3 6 = plane_1_3_6 := by rfl
theorem plane_1_3_6_sound (p : Point) (h : ClosedCell 3 (view 1 p)) :
    plane_1_3_6.rational.contains p := by
  rw [← plane_1_3_6_eq]
  exact sourcePlane_sound 1 3 6 p h

def plane_1_3_10 : IntegerPlane := ⟨1842436000000, 2505748000000, 1109879215428⟩
theorem plane_1_3_10_eq : sourcePlane 1 3 10 = plane_1_3_10 := by rfl
theorem plane_1_3_10_sound (p : Point) (h : ClosedCell 3 (view 1 p)) :
    plane_1_3_10.rational.contains p := by
  rw [← plane_1_3_10_eq]
  exact sourcePlane_sound 1 3 10 p h

def plane_1_3_11 : IntegerPlane := ⟨(-202532000000), 1861776000000, 383371739447⟩
theorem plane_1_3_11_eq : sourcePlane 1 3 11 = plane_1_3_11 := by rfl
theorem plane_1_3_11_sound (p : Point) (h : ClosedCell 3 (view 1 p)) :
    plane_1_3_11.rational.contains p := by
  rw [← plane_1_3_11_eq]
  exact sourcePlane_sound 1 3 11 p h

def plane_1_4_4 : IntegerPlane := ⟨(-15204000000), (-2139684000000), (-584166228432)⟩
theorem plane_1_4_4_eq : sourcePlane 1 4 4 = plane_1_4_4 := by rfl
theorem plane_1_4_4_sound (p : Point) (h : ClosedCell 4 (view 1 p)) :
    plane_1_4_4.rational.contains p := by
  rw [← plane_1_4_4_eq]
  exact sourcePlane_sound 1 4 4 p h

def plane_1_4_9 : IntegerPlane := ⟨(-2144520000000), (-699568000000), (-1885510108648)⟩
theorem plane_1_4_9_eq : sourcePlane 1 4 9 = plane_1_4_9 := by rfl
theorem plane_1_4_9_sound (p : Point) (h : ClosedCell 4 (view 1 p)) :
    plane_1_4_9.rational.contains p := by
  rw [← plane_1_4_9_eq]
  exact sourcePlane_sound 1 4 9 p h

def plane_1_4_10 : IntegerPlane := ⟨(-4257332000000), 125148000000, (-2634551273104)⟩
theorem plane_1_4_10_eq : sourcePlane 1 4 10 = plane_1_4_10 := by rfl
theorem plane_1_4_10_sound (p : Point) (h : ClosedCell 4 (view 1 p)) :
    plane_1_4_10.rational.contains p := by
  rw [← plane_1_4_10_eq]
  exact sourcePlane_sound 1 4 10 p h

def plane_1_4_12 : IntegerPlane := ⟨(-48252000000), 2112760000000, 1081757250915⟩
theorem plane_1_4_12_eq : sourcePlane 1 4 12 = plane_1_4_12 := by rfl
theorem plane_1_4_12_sound (p : Point) (h : ClosedCell 4 (view 1 p)) :
    plane_1_4_12.rational.contains p := by
  rw [← plane_1_4_12_eq]
  exact sourcePlane_sound 1 4 12 p h

def plane_1_4_13 : IntegerPlane := ⟨(-2093220000000), 1468788000000, (-880675273104)⟩
theorem plane_1_4_13_eq : sourcePlane 1 4 13 = plane_1_4_13 := by rfl
theorem plane_1_4_13_sound (p : Point) (h : ClosedCell 4 (view 1 p)) :
    plane_1_4_13.rational.contains p := by
  rw [← plane_1_4_13_eq]
  exact sourcePlane_sound 1 4 13 p h

def plane_1_5_4 : IntegerPlane := ⟨2129316000000, (-1440116000000), 1301343880216⟩
theorem plane_1_5_4_eq : sourcePlane 1 5 4 = plane_1_5_4 := by rfl
theorem plane_1_5_4_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_4.rational.contains p := by
  rw [← plane_1_5_4_eq]
  exact sourcePlane_sound 1 5 4 p h

def plane_1_5_5 : IntegerPlane := ⟨(-16372000000), (-2139440000000), (-393704847425)⟩
theorem plane_1_5_5_eq : sourcePlane 1 5 5 = plane_1_5_5 := by rfl
theorem plane_1_5_5_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_5.rational.contains p := by
  rw [← plane_1_5_5_eq]
  exact sourcePlane_sound 1 5 5 p h

def plane_1_5_6 : IntegerPlane := ⟨(-2099728000000), (-1393416000000), (-1359544139484)⟩
theorem plane_1_5_6_eq : sourcePlane 1 5 6 = plane_1_5_6 := by rfl
theorem plane_1_5_6_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_6.rational.contains p := by
  rw [← plane_1_5_6_eq]
  exact sourcePlane_sound 1 5 6 p h

def plane_1_5_8 : IntegerPlane := ⟨2144520000000, 699568000000, 1885510108648⟩
theorem plane_1_5_8_eq : sourcePlane 1 5 8 = plane_1_5_8 := by rfl
theorem plane_1_5_8_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_8.rational.contains p := by
  rw [← plane_1_5_8_eq]
  exact sourcePlane_sound 1 5 8 p h

def plane_1_5_10 : IntegerPlane := ⟨(-2112812000000), 824716000000, (-749041164456)⟩
theorem plane_1_5_10_eq : sourcePlane 1 5 10 = plane_1_5_10 := by rfl
theorem plane_1_5_10_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_10.rational.contains p := by
  rw [← plane_1_5_10_eq]
  exact sourcePlane_sound 1 5 10 p h

def plane_1_5_11 : IntegerPlane := ⟨(-4157780000000), 180744000000, (-1475548640437)⟩
theorem plane_1_5_11_eq : sourcePlane 1 5 11 = plane_1_5_11 := by rfl
theorem plane_1_5_11_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_11.rational.contains p := by
  rw [← plane_1_5_11_eq]
  exact sourcePlane_sound 1 5 11 p h

def plane_1_5_13 : IntegerPlane := ⟨51300000000, 2168356000000, 1004834835544⟩
theorem plane_1_5_13_eq : sourcePlane 1 5 13 = plane_1_5_13 := by rfl
theorem plane_1_5_13_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_13.rational.contains p := by
  rw [← plane_1_5_13_eq]
  exact sourcePlane_sound 1 5 13 p h

def plane_1_5_14 : IntegerPlane := ⟨(-2061512000000), 2993072000000, 465780000000⟩
theorem plane_1_5_14_eq : sourcePlane 1 5 14 = plane_1_5_14 := by rfl
theorem plane_1_5_14_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_14.rational.contains p := by
  rw [← plane_1_5_14_eq]
  exact sourcePlane_sound 1 5 14 p h

def plane_1_5_15 : IntegerPlane := ⟨(-4206032000000), 2293504000000, (-492797891352)⟩
theorem plane_1_5_15_eq : sourcePlane 1 5 15 = plane_1_5_15 := by rfl
theorem plane_1_5_15_sound (p : Point) (h : ClosedCell 5 (view 1 p)) :
    plane_1_5_15.rational.contains p := by
  rw [← plane_1_5_15_eq]
  exact sourcePlane_sound 1 5 15 p h

def plane_1_6_6 : IntegerPlane := ⟨13084000000, (-2218132000000), (-610502975028)⟩
theorem plane_1_6_6_eq : sourcePlane 1 6 6 = plane_1_6_6 := by rfl
theorem plane_1_6_6_sound (p : Point) (h : ClosedCell 6 (view 1 p)) :
    plane_1_6_6.rational.contains p := by
  rw [← plane_1_6_6_eq]
  exact sourcePlane_sound 1 6 6 p h

def plane_1_6_8 : IntegerPlane := ⟨4257332000000, (-125148000000), 2634551273104⟩
theorem plane_1_6_8_eq : sourcePlane 1 6 8 = plane_1_6_8 := by rfl
theorem plane_1_6_8_sound (p : Point) (h : ClosedCell 6 (view 1 p)) :
    plane_1_6_8.rational.contains p := by
  rw [← plane_1_6_8_eq]
  exact sourcePlane_sound 1 6 8 p h

def plane_1_6_9 : IntegerPlane := ⟨2112812000000, (-824716000000), 749041164456⟩
theorem plane_1_6_9_eq : sourcePlane 1 6 9 = plane_1_6_9 := by rfl
theorem plane_1_6_9_sound (p : Point) (h : ClosedCell 6 (view 1 p)) :
    plane_1_6_9.rational.contains p := by
  rw [← plane_1_6_9_eq]
  exact sourcePlane_sound 1 6 9 p h

def plane_1_6_11 : IntegerPlane := ⟨(-2044968000000), (-643972000000), (-726507475981)⟩
theorem plane_1_6_11_eq : sourcePlane 1 6 11 = plane_1_6_11 := by rfl
theorem plane_1_6_11_sound (p : Point) (h : ClosedCell 6 (view 1 p)) :
    plane_1_6_11.rational.contains p := by
  rw [← plane_1_6_11_eq]
  exact sourcePlane_sound 1 6 11 p h

def plane_1_6_13 : IntegerPlane := ⟨2164112000000, 1343640000000, 1753876000000⟩
theorem plane_1_6_13_eq : sourcePlane 1 6 13 = plane_1_6_13 := by rfl
theorem plane_1_6_13_sound (p : Point) (h : ClosedCell 6 (view 1 p)) :
    plane_1_6_13.rational.contains p := by
  rw [← plane_1_6_13_eq]
  exact sourcePlane_sound 1 6 13 p h

def plane_1_6_14 : IntegerPlane := ⟨51300000000, 2168356000000, 1214821164456⟩
theorem plane_1_6_14_eq : sourcePlane 1 6 14 = plane_1_6_14 := by rfl
theorem plane_1_6_14_sound (p : Point) (h : ClosedCell 6 (view 1 p)) :
    plane_1_6_14.rational.contains p := by
  rw [← plane_1_6_14_eq]
  exact sourcePlane_sound 1 6 14 p h

def plane_1_6_15 : IntegerPlane := ⟨(-2093220000000), 1468788000000, 256243273104⟩
theorem plane_1_6_15_eq : sourcePlane 1 6 15 = plane_1_6_15 := by rfl
theorem plane_1_6_15_sound (p : Point) (h : ClosedCell 6 (view 1 p)) :
    plane_1_6_15.rational.contains p := by
  rw [← plane_1_6_15_eq]
  exact sourcePlane_sound 1 6 15 p h

def plane_1_7_6 : IntegerPlane := ⟨2058052000000, (-1574160000000), 116004500953⟩
theorem plane_1_7_6_eq : sourcePlane 1 7 6 = plane_1_7_6 := by rfl
theorem plane_1_7_6_sound (p : Point) (h : ClosedCell 7 (view 1 p)) :
    plane_1_7_6.rational.contains p := by
  rw [← plane_1_7_6_eq]
  exact sourcePlane_sound 1 7 6 p h

def plane_1_7_7 : IntegerPlane := ⟨202532000000, (-1861776000000), (-383371739447)⟩
theorem plane_1_7_7_eq : sourcePlane 1 7 7 = plane_1_7_7 := by rfl
theorem plane_1_7_7_sound (p : Point) (h : ClosedCell 7 (view 1 p)) :
    plane_1_7_7.rational.contains p := by
  rw [← plane_1_7_7_eq]
  exact sourcePlane_sound 1 7 7 p h

def plane_1_7_8 : IntegerPlane := ⟨6302300000000, 518824000000, 3361058749085⟩
theorem plane_1_7_8_eq : sourcePlane 1 7 8 = plane_1_7_8 := by rfl
theorem plane_1_7_8_sound (p : Point) (h : ClosedCell 7 (view 1 p)) :
    plane_1_7_8.rational.contains p := by
  rw [← plane_1_7_8_eq]
  exact sourcePlane_sound 1 7 8 p h

def plane_1_7_9 : IntegerPlane := ⟨4157780000000, (-180744000000), 1475548640437⟩
theorem plane_1_7_9_eq : sourcePlane 1 7 9 = plane_1_7_9 := by rfl
theorem plane_1_7_9_sound (p : Point) (h : ClosedCell 7 (view 1 p)) :
    plane_1_7_9.rational.contains p := by
  rw [← plane_1_7_9_eq]
  exact sourcePlane_sound 1 7 9 p h

def plane_1_7_10 : IntegerPlane := ⟨2044968000000, 643972000000, 726507475981⟩
theorem plane_1_7_10_eq : sourcePlane 1 7 10 = plane_1_7_10 := by rfl
theorem plane_1_7_10_sound (p : Point) (h : ClosedCell 7 (view 1 p)) :
    plane_1_7_10.rational.contains p := by
  rw [← plane_1_7_10_eq]
  exact sourcePlane_sound 1 7 10 p h

def plane_1_7_15 : IntegerPlane := ⟨(-48252000000), 2112760000000, 982750749085⟩
theorem plane_1_7_15_eq : sourcePlane 1 7 15 = plane_1_7_15 := by rfl
theorem plane_1_7_15_sound (p : Point) (h : ClosedCell 7 (view 1 p)) :
    plane_1_7_15.rational.contains p := by
  rw [← plane_1_7_15_eq]
  exact sourcePlane_sound 1 7 15 p h

def plane_1_7_19 : IntegerPlane := ⟨(-33048000000), 4252444000000, 2553472520653⟩
theorem plane_1_7_19_eq : sourcePlane 1 7 19 = plane_1_7_19 := by rfl
theorem plane_1_7_19_sound (p : Point) (h : ClosedCell 7 (view 1 p)) :
    plane_1_7_19.rational.contains p := by
  rw [← plane_1_7_19_eq]
  exact sourcePlane_sound 1 7 19 p h

def plane_1_8_4 : IntegerPlane := ⟨33048000000, (-4252444000000), (-1665923479347)⟩
theorem plane_1_8_4_eq : sourcePlane 1 8 4 = plane_1_8_4 := by rfl
theorem plane_1_8_4_sound (p : Point) (h : ClosedCell 8 (view 1 p)) :
    plane_1_8_4.rational.contains p := by
  rw [← plane_1_8_4_eq]
  exact sourcePlane_sound 1 8 4 p h

def plane_1_8_8 : IntegerPlane := ⟨48252000000, (-2112760000000), (-1081757250915)⟩
theorem plane_1_8_8_eq : sourcePlane 1 8 8 = plane_1_8_8 := by rfl
theorem plane_1_8_8_sound (p : Point) (h : ClosedCell 8 (view 1 p)) :
    plane_1_8_8.rational.contains p := by
  rw [← plane_1_8_8_eq]
  exact sourcePlane_sound 1 8 8 p h

def plane_1_8_13 : IntegerPlane := ⟨(-2044968000000), (-643972000000), (-1962432524019)⟩
theorem plane_1_8_13_eq : sourcePlane 1 8 13 = plane_1_8_13 := by rfl
theorem plane_1_8_13_sound (p : Point) (h : ClosedCell 8 (view 1 p)) :
    plane_1_8_13.rational.contains p := by
  rw [← plane_1_8_13_eq]
  exact sourcePlane_sound 1 8 13 p h

def plane_1_8_14 : IntegerPlane := ⟨(-4157780000000), 180744000000, (-2501487359563)⟩
theorem plane_1_8_14_eq : sourcePlane 1 8 14 = plane_1_8_14 := by rfl
theorem plane_1_8_14_sound (p : Point) (h : ClosedCell 8 (view 1 p)) :
    plane_1_8_14.rational.contains p := by
  rw [← plane_1_8_14_eq]
  exact sourcePlane_sound 1 8 14 p h

def plane_1_8_15 : IntegerPlane := ⟨(-6302300000000), (-518824000000), (-3460065250915)⟩
theorem plane_1_8_15_eq : sourcePlane 1 8 15 = plane_1_8_15 := by rfl
theorem plane_1_8_15_sound (p : Point) (h : ClosedCell 8 (view 1 p)) :
    plane_1_8_15.rational.contains p := by
  rw [← plane_1_8_15_eq]
  exact sourcePlane_sound 1 8 15 p h

def plane_1_8_16 : IntegerPlane := ⟨(-202532000000), 1861776000000, 1275872260553⟩
theorem plane_1_8_16_eq : sourcePlane 1 8 16 = plane_1_8_16 := by rfl
theorem plane_1_8_16_sound (p : Point) (h : ClosedCell 8 (view 1 p)) :
    plane_1_8_16.rational.contains p := by
  rw [← plane_1_8_16_eq]
  exact sourcePlane_sound 1 8 16 p h

def plane_1_8_17 : IntegerPlane := ⟨(-2058052000000), 1574160000000, (-367887499047)⟩
theorem plane_1_8_17_eq : sourcePlane 1 8 17 = plane_1_8_17 := by rfl
theorem plane_1_8_17_sound (p : Point) (h : ClosedCell 8 (view 1 p)) :
    plane_1_8_17.rational.contains p := by
  rw [← plane_1_8_17_eq]
  exact sourcePlane_sound 1 8 17 p h

def plane_1_9_4 : IntegerPlane := ⟨2078016000000, (-3608472000000), 296509044672⟩
theorem plane_1_9_4_eq : sourcePlane 1 9 4 = plane_1_9_4 := by rfl
theorem plane_1_9_4_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_4.rational.contains p := by
  rw [← plane_1_9_4_eq]
  exact sourcePlane_sound 1 9 4 p h

def plane_1_9_8 : IntegerPlane := ⟨2093220000000, (-1468788000000), 880675273104⟩
theorem plane_1_9_8_eq : sourcePlane 1 9 8 = plane_1_9_8 := by rfl
theorem plane_1_9_8_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_8.rational.contains p := by
  rw [← plane_1_9_8_eq]
  exact sourcePlane_sound 1 9 8 p h

def plane_1_9_9 : IntegerPlane := ⟨(-51300000000), (-2168356000000), (-1004834835544)⟩
theorem plane_1_9_9_eq : sourcePlane 1 9 9 = plane_1_9_9 := by rfl
theorem plane_1_9_9_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_9.rational.contains p := by
  rw [← plane_1_9_9_eq]
  exact sourcePlane_sound 1 9 9 p h

def plane_1_9_10 : IntegerPlane := ⟨(-2164112000000), (-1343640000000), (-1753876000000)⟩
theorem plane_1_9_10_eq : sourcePlane 1 9 10 = plane_1_9_10 := by rfl
theorem plane_1_9_10_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_10.rational.contains p := by
  rw [← plane_1_9_10_eq]
  exact sourcePlane_sound 1 9 10 p h

def plane_1_9_12 : IntegerPlane := ⟨2044968000000, 643972000000, 1962432524019⟩
theorem plane_1_9_12_eq : sourcePlane 1 9 12 = plane_1_9_12 := by rfl
theorem plane_1_9_12_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_12.rational.contains p := by
  rw [← plane_1_9_12_eq]
  exact sourcePlane_sound 1 9 12 p h

def plane_1_9_14 : IntegerPlane := ⟨(-2112812000000), 824716000000, (-539054835544)⟩
theorem plane_1_9_14_eq : sourcePlane 1 9 14 = plane_1_9_14 := by rfl
theorem plane_1_9_14_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_14.rational.contains p := by
  rw [← plane_1_9_14_eq]
  exact sourcePlane_sound 1 9 14 p h

def plane_1_9_15 : IntegerPlane := ⟨(-4257332000000), 125148000000, (-1497632726896)⟩
theorem plane_1_9_15_eq : sourcePlane 1 9 15 = plane_1_9_15 := by rfl
theorem plane_1_9_15_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_15.rational.contains p := by
  rw [← plane_1_9_15_eq]
  exact sourcePlane_sound 1 9 15 p h

def plane_1_9_17 : IntegerPlane := ⟨(-13084000000), 2218132000000, 1594545024972⟩
theorem plane_1_9_17_eq : sourcePlane 1 9 17 = plane_1_9_17 := by rfl
theorem plane_1_9_17_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_17.rational.contains p := by
  rw [← plane_1_9_17_eq]
  exact sourcePlane_sound 1 9 17 p h

def plane_1_9_19 : IntegerPlane := ⟨(-4242128000000), 2264832000000, 73089044672⟩
theorem plane_1_9_19_eq : sourcePlane 1 9 19 = plane_1_9_19 := by rfl
theorem plane_1_9_19_sound (p : Point) (h : ClosedCell 9 (view 1 p)) :
    plane_1_9_19.rational.contains p := by
  rw [← plane_1_9_19_eq]
  exact sourcePlane_sound 1 9 19 p h

def plane_1_10_10 : IntegerPlane := ⟨(-51300000000), (-2168356000000), (-1214821164456)⟩
theorem plane_1_10_10_eq : sourcePlane 1 10 10 = plane_1_10_10 := by rfl
theorem plane_1_10_10_sound (p : Point) (h : ClosedCell 10 (view 1 p)) :
    plane_1_10_10.rational.contains p := by
  rw [← plane_1_10_10_eq]
  exact sourcePlane_sound 1 10 10 p h

def plane_1_10_12 : IntegerPlane := ⟨4157780000000, (-180744000000), 2501487359563⟩
theorem plane_1_10_12_eq : sourcePlane 1 10 12 = plane_1_10_12 := by rfl
theorem plane_1_10_12_sound (p : Point) (h : ClosedCell 10 (view 1 p)) :
    plane_1_10_12.rational.contains p := by
  rw [← plane_1_10_12_eq]
  exact sourcePlane_sound 1 10 12 p h

def plane_1_10_13 : IntegerPlane := ⟨2112812000000, (-824716000000), 539054835544⟩
theorem plane_1_10_13_eq : sourcePlane 1 10 13 = plane_1_10_13 := by rfl
theorem plane_1_10_13_sound (p : Point) (h : ClosedCell 10 (view 1 p)) :
    plane_1_10_13.rational.contains p := by
  rw [← plane_1_10_13_eq]
  exact sourcePlane_sound 1 10 13 p h

def plane_1_10_15 : IntegerPlane := ⟨(-2144520000000), (-699568000000), (-958577891352)⟩
theorem plane_1_10_15_eq : sourcePlane 1 10 15 = plane_1_10_15 := by rfl
theorem plane_1_10_15_sound (p : Point) (h : ClosedCell 10 (view 1 p)) :
    plane_1_10_15.rational.contains p := by
  rw [← plane_1_10_15_eq]
  exact sourcePlane_sound 1 10 15 p h

def plane_1_10_17 : IntegerPlane := ⟨2099728000000, 1393416000000, 2133599860516⟩
theorem plane_1_10_17_eq : sourcePlane 1 10 17 = plane_1_10_17 := by rfl
theorem plane_1_10_17_sound (p : Point) (h : ClosedCell 10 (view 1 p)) :
    plane_1_10_17.rational.contains p := by
  rw [← plane_1_10_17_eq]
  exact sourcePlane_sound 1 10 17 p h

def plane_1_10_18 : IntegerPlane := ⟨16372000000, 2139440000000, 1762107152575⟩
theorem plane_1_10_18_eq : sourcePlane 1 10 18 = plane_1_10_18 := by rfl
theorem plane_1_10_18_sound (p : Point) (h : ClosedCell 10 (view 1 p)) :
    plane_1_10_18.rational.contains p := by
  rw [← plane_1_10_18_eq]
  exact sourcePlane_sound 1 10 18 p h

def plane_1_10_19 : IntegerPlane := ⟨(-2129316000000), 1440116000000, 612143880216⟩
theorem plane_1_10_19_eq : sourcePlane 1 10 19 = plane_1_10_19 := by rfl
theorem plane_1_10_19_sound (p : Point) (h : ClosedCell 10 (view 1 p)) :
    plane_1_10_19.rational.contains p := by
  rw [← plane_1_10_19_eq]
  exact sourcePlane_sound 1 10 19 p h

def plane_1_11_5 : IntegerPlane := ⟨4189660000000, (-4432944000000), 99093043927⟩
theorem plane_1_11_5_eq : sourcePlane 1 11 5 = plane_1_11_5 := by rfl
theorem plane_1_11_5_sound (p : Point) (h : ClosedCell 11 (view 1 p)) :
    plane_1_11_5.rational.contains p := by
  rw [← plane_1_11_5_eq]
  exact sourcePlane_sound 1 11 5 p h

def plane_1_11_10 : IntegerPlane := ⟨2093220000000, (-1468788000000), (-256243273104)⟩
theorem plane_1_11_10_eq : sourcePlane 1 11 10 = plane_1_11_10 := by rfl
theorem plane_1_11_10_sound (p : Point) (h : ClosedCell 11 (view 1 p)) :
    plane_1_11_10.rational.contains p := by
  rw [← plane_1_11_10_eq]
  exact sourcePlane_sound 1 11 10 p h

def plane_1_11_11 : IntegerPlane := ⟨48252000000, (-2112760000000), (-982750749085)⟩
theorem plane_1_11_11_eq : sourcePlane 1 11 11 = plane_1_11_11 := by rfl
theorem plane_1_11_11_sound (p : Point) (h : ClosedCell 11 (view 1 p)) :
    plane_1_11_11.rational.contains p := by
  rw [← plane_1_11_11_eq]
  exact sourcePlane_sound 1 11 11 p h

def plane_1_11_13 : IntegerPlane := ⟨4257332000000, (-125148000000), 1497632726896⟩
theorem plane_1_11_13_eq : sourcePlane 1 11 13 = plane_1_11_13 := by rfl
theorem plane_1_11_13_sound (p : Point) (h : ClosedCell 11 (view 1 p)) :
    plane_1_11_13.rational.contains p := by
  rw [← plane_1_11_13_eq]
  exact sourcePlane_sound 1 11 13 p h

def plane_1_11_14 : IntegerPlane := ⟨2144520000000, 699568000000, 958577891352⟩
theorem plane_1_11_14_eq : sourcePlane 1 11 14 = plane_1_11_14 := by rfl
theorem plane_1_11_14_sound (p : Point) (h : ClosedCell 11 (view 1 p)) :
    plane_1_11_14.rational.contains p := by
  rw [← plane_1_11_14_eq]
  exact sourcePlane_sound 1 11 14 p h

def plane_1_11_19 : IntegerPlane := ⟨15204000000, 2139684000000, 1570721771568⟩
theorem plane_1_11_19_eq : sourcePlane 1 11 19 = plane_1_11_19 := by rfl
theorem plane_1_11_19_sound (p : Point) (h : ClosedCell 11 (view 1 p)) :
    plane_1_11_19.rational.contains p := by
  rw [← plane_1_11_19_eq]
  exact sourcePlane_sound 1 11 19 p h

def plane_1_12_8 : IntegerPlane := ⟨250784000000, (-3974536000000), (-2357629511468)⟩
theorem plane_1_12_8_eq : sourcePlane 1 12 8 = plane_1_12_8 := by rfl
theorem plane_1_12_8_sound (p : Point) (h : ClosedCell 12 (view 1 p)) :
    plane_1_12_8.rational.contains p := by
  rw [← plane_1_12_8_eq]
  exact sourcePlane_sound 1 12 8 p h

def plane_1_12_12 : IntegerPlane := ⟨202532000000, (-1861776000000), (-1275872260553)⟩
theorem plane_1_12_12_eq : sourcePlane 1 12 12 = plane_1_12_12 := by rfl
theorem plane_1_12_12_sound (p : Point) (h : ClosedCell 12 (view 1 p)) :
    plane_1_12_12.rational.contains p := by
  rw [← plane_1_12_12_eq]
  exact sourcePlane_sound 1 12 12 p h

def plane_1_12_17 : IntegerPlane := ⟨(-1855520000000), (-287616000000), (-1643759759600)⟩
theorem plane_1_12_17_eq : sourcePlane 1 12 17 = plane_1_12_17 := by rfl
theorem plane_1_12_17_sound (p : Point) (h : ClosedCell 12 (view 1 p)) :
    plane_1_12_17.rational.contains p := by
  rw [← plane_1_12_17_eq]
  exact sourcePlane_sound 1 12 17 p h

def plane_1_12_18 : IntegerPlane := ⟨(-3938876000000), 458408000000, (-2015252467541)⟩
theorem plane_1_12_18_eq : sourcePlane 1 12 18 = plane_1_12_18 := by rfl
theorem plane_1_12_18_sound (p : Point) (h : ClosedCell 12 (view 1 p)) :
    plane_1_12_18.rational.contains p := by
  rw [← plane_1_12_18_eq]
  exact sourcePlane_sound 1 12 18 p h

def plane_1_12_19 : IntegerPlane := ⟨(-6084564000000), (-240916000000), (-3165215739900)⟩
theorem plane_1_12_19_eq : sourcePlane 1 12 19 = plane_1_12_19 := by rfl
theorem plane_1_12_19_sound (p : Point) (h : ClosedCell 12 (view 1 p)) :
    plane_1_12_19.rational.contains p := by
  rw [← plane_1_12_19_eq]
  exact sourcePlane_sound 1 12 19 p h

def plane_1_13_12 : IntegerPlane := ⟨2058052000000, (-1574160000000), 367887499047⟩
theorem plane_1_13_12_eq : sourcePlane 1 13 12 = plane_1_13_12 := by rfl
theorem plane_1_13_12_sound (p : Point) (h : ClosedCell 13 (view 1 p)) :
    plane_1_13_12.rational.contains p := by
  rw [← plane_1_13_12_eq]
  exact sourcePlane_sound 1 13 12 p h

def plane_1_13_13 : IntegerPlane := ⟨13084000000, (-2218132000000), (-1594545024972)⟩
theorem plane_1_13_13_eq : sourcePlane 1 13 13 = plane_1_13_13 := by rfl
theorem plane_1_13_13_sound (p : Point) (h : ClosedCell 13 (view 1 p)) :
    plane_1_13_13.rational.contains p := by
  rw [← plane_1_13_13_eq]
  exact sourcePlane_sound 1 13 13 p h

def plane_1_13_14 : IntegerPlane := ⟨(-2099728000000), (-1393416000000), (-2133599860516)⟩
theorem plane_1_13_14_eq : sourcePlane 1 13 14 = plane_1_13_14 := by rfl
theorem plane_1_13_14_sound (p : Point) (h : ClosedCell 13 (view 1 p)) :
    plane_1_13_14.rational.contains p := by
  rw [← plane_1_13_14_eq]
  exact sourcePlane_sound 1 13 14 p h

def plane_1_13_16 : IntegerPlane := ⟨1855520000000, 287616000000, 1643759759600⟩
theorem plane_1_13_16_eq : sourcePlane 1 13 16 = plane_1_13_16 := by rfl
theorem plane_1_13_16_sound (p : Point) (h : ClosedCell 13 (view 1 p)) :
    plane_1_13_16.rational.contains p := by
  rw [← plane_1_13_16_eq]
  exact sourcePlane_sound 1 13 16 p h

def plane_1_13_18 : IntegerPlane := ⟨(-2083356000000), 746024000000, (-371492707941)⟩
theorem plane_1_13_18_eq : sourcePlane 1 13 18 = plane_1_13_18 := by rfl
theorem plane_1_13_18_sound (p : Point) (h : ClosedCell 13 (view 1 p)) :
    plane_1_13_18.rational.contains p := by
  rw [← plane_1_13_18_eq]
  exact sourcePlane_sound 1 13 18 p h

def plane_1_13_19 : IntegerPlane := ⟨(-4229044000000), 46700000000, (-1521455980300)⟩
theorem plane_1_13_19_eq : sourcePlane 1 13 19 = plane_1_13_19 := by rfl
theorem plane_1_13_19_sound (p : Point) (h : ClosedCell 13 (view 1 p)) :
    plane_1_13_19.rational.contains p := by
  rw [← plane_1_13_19_eq]
  exact sourcePlane_sound 1 13 19 p h

def plane_1_14_6 : IntegerPlane := ⟨(-54588000000), (-6525928000000), (-3587431292059)⟩
theorem plane_1_14_6_eq : sourcePlane 1 14 6 = plane_1_14_6 := by rfl
theorem plane_1_14_6_sound (p : Point) (h : ClosedCell 14 (view 1 p)) :
    plane_1_14_6.rational.contains p := by
  rw [← plane_1_14_6_eq]
  exact sourcePlane_sound 1 14 6 p h

def plane_1_14_14 : IntegerPlane := ⟨(-16372000000), (-2139440000000), (-1762107152575)⟩
theorem plane_1_14_14_eq : sourcePlane 1 14 14 = plane_1_14_14 := by rfl
theorem plane_1_14_14_sound (p : Point) (h : ClosedCell 14 (view 1 p)) :
    plane_1_14_14.rational.contains p := by
  rw [← plane_1_14_14_eq]
  exact sourcePlane_sound 1 14 14 p h

def plane_1_14_16 : IntegerPlane := ⟨3938876000000, (-458408000000), 2015252467541⟩
theorem plane_1_14_16_eq : sourcePlane 1 14 16 = plane_1_14_16 := by rfl
theorem plane_1_14_16_sound (p : Point) (h : ClosedCell 14 (view 1 p)) :
    plane_1_14_16.rational.contains p := by
  rw [← plane_1_14_16_eq]
  exact sourcePlane_sound 1 14 16 p h

def plane_1_14_17 : IntegerPlane := ⟨2083356000000, (-746024000000), 371492707941⟩
theorem plane_1_14_17_eq : sourcePlane 1 14 17 = plane_1_14_17 := by rfl
theorem plane_1_14_17_sound (p : Point) (h : ClosedCell 14 (view 1 p)) :
    plane_1_14_17.rational.contains p := by
  rw [← plane_1_14_17_eq]
  exact sourcePlane_sound 1 14 17 p h

def plane_1_14_19 : IntegerPlane := ⟨(-2145688000000), (-699324000000), (-1149963272359)⟩
theorem plane_1_14_19_eq : sourcePlane 1 14 19 = plane_1_14_19 := by rfl
theorem plane_1_14_19_sound (p : Point) (h : ClosedCell 14 (view 1 p)) :
    plane_1_14_19.rational.contains p := by
  rw [← plane_1_14_19_eq]
  exact sourcePlane_sound 1 14 19 p h

def plane_1_15_13 : IntegerPlane := ⟨4242128000000, (-2264832000000), (-73089044672)⟩
theorem plane_1_15_13_eq : sourcePlane 1 15 13 = plane_1_15_13 := by rfl
theorem plane_1_15_13_sound (p : Point) (h : ClosedCell 15 (view 1 p)) :
    plane_1_15_13.rational.contains p := by
  rw [← plane_1_15_13_eq]
  exact sourcePlane_sound 1 15 13 p h

def plane_1_15_14 : IntegerPlane := ⟨2129316000000, (-1440116000000), (-612143880216)⟩
theorem plane_1_15_14_eq : sourcePlane 1 15 14 = plane_1_15_14 := by rfl
theorem plane_1_15_14_sound (p : Point) (h : ClosedCell 15 (view 1 p)) :
    plane_1_15_14.rational.contains p := by
  rw [← plane_1_15_14_eq]
  exact sourcePlane_sound 1 15 14 p h

def plane_1_15_15 : IntegerPlane := ⟨(-15204000000), (-2139684000000), (-1570721771568)⟩
theorem plane_1_15_15_eq : sourcePlane 1 15 15 = plane_1_15_15 := by rfl
theorem plane_1_15_15_sound (p : Point) (h : ClosedCell 15 (view 1 p)) :
    plane_1_15_15.rational.contains p := by
  rw [← plane_1_15_15_eq]
  exact sourcePlane_sound 1 15 15 p h

def plane_1_15_17 : IntegerPlane := ⟨4229044000000, (-46700000000), 1521455980300⟩
theorem plane_1_15_17_eq : sourcePlane 1 15 17 = plane_1_15_17 := by rfl
theorem plane_1_15_17_sound (p : Point) (h : ClosedCell 15 (view 1 p)) :
    plane_1_15_17.rational.contains p := by
  rw [← plane_1_15_17_eq]
  exact sourcePlane_sound 1 15 17 p h

def plane_1_15_18 : IntegerPlane := ⟨2145688000000, 699324000000, 1149963272359⟩
theorem plane_1_15_18_eq : sourcePlane 1 15 18 = plane_1_15_18 := by rfl
theorem plane_1_15_18_sound (p : Point) (h : ClosedCell 15 (view 1 p)) :
    plane_1_15_18.rational.contains p := by
  rw [← plane_1_15_18_eq]
  exact sourcePlane_sound 1 15 18 p h

end ElevenSquare.Pending.T04Completeness
