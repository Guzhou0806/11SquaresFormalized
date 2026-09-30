import ElevenSquare.Tasks.T04.Completeness.Support

/-! Memoized exact original halfplanes for view 0. Each lookup identity is kernel-checked by reflexivity. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxRecDepth 10000

def plane_0_0_0 : IntegerPlane := ⟨(-1), 0, 0⟩
theorem plane_0_0_0_eq : sourcePlane 0 0 0 = plane_0_0_0 := by rfl
theorem plane_0_0_0_sound (p : Point) (h : ClosedCell 0 (view 0 p)) :
    plane_0_0_0.rational.contains p := by
  rw [← plane_0_0_0_eq]
  exact sourcePlane_sound 0 0 0 p h

def plane_0_0_2 : IntegerPlane := ⟨0, (-1), 0⟩
theorem plane_0_0_2_eq : sourcePlane 0 0 2 = plane_0_0_2 := by rfl
theorem plane_0_0_2_sound (p : Point) (h : ClosedCell 0 (view 0 p)) :
    plane_0_0_2.rational.contains p := by
  rw [← plane_0_0_2_eq]
  exact sourcePlane_sound 0 0 2 p h

def plane_0_0_5 : IntegerPlane := ⟨2145688000000, (-699324000000), 450639272359⟩
theorem plane_0_0_5_eq : sourcePlane 0 0 5 = plane_0_0_5 := by rfl
theorem plane_0_0_5_sound (p : Point) (h : ClosedCell 0 (view 0 p)) :
    plane_0_0_5.rational.contains p := by
  rw [← plane_0_0_5_eq]
  exact sourcePlane_sound 0 0 5 p h

def plane_0_0_6 : IntegerPlane := ⟨4229044000000, 46700000000, 1568155980300⟩
theorem plane_0_0_6_eq : sourcePlane 0 0 6 = plane_0_0_6 := by rfl
theorem plane_0_0_6_sound (p : Point) (h : ClosedCell 0 (view 0 p)) :
    plane_0_0_6.rational.contains p := by
  rw [← plane_0_0_6_eq]
  exact sourcePlane_sound 0 0 6 p h

def plane_0_0_8 : IntegerPlane := ⟨(-15204000000), 2139684000000, 568962228432⟩
theorem plane_0_0_8_eq : sourcePlane 0 0 8 = plane_0_0_8 := by rfl
theorem plane_0_0_8_sound (p : Point) (h : ClosedCell 0 (view 0 p)) :
    plane_0_0_8.rational.contains p := by
  rw [← plane_0_0_8_eq]
  exact sourcePlane_sound 0 0 8 p h

def plane_0_0_9 : IntegerPlane := ⟨2129316000000, 1440116000000, 827972119784⟩
theorem plane_0_0_9_eq : sourcePlane 0 0 9 = plane_0_0_9 := by rfl
theorem plane_0_0_9_sound (p : Point) (h : ClosedCell 0 (view 0 p)) :
    plane_0_0_9.rational.contains p := by
  rw [← plane_0_0_9_eq]
  exact sourcePlane_sound 0 0 9 p h

def plane_0_1_2 : IntegerPlane := ⟨0, (-1), 0⟩
theorem plane_0_1_2_eq : sourcePlane 0 1 2 = plane_0_1_2 := by rfl
theorem plane_0_1_2_sound (p : Point) (h : ClosedCell 1 (view 0 p)) :
    plane_0_1_2.rational.contains p := by
  rw [← plane_0_1_2_eq]
  exact sourcePlane_sound 0 1 2 p h

def plane_0_1_4 : IntegerPlane := ⟨(-2145688000000), 699324000000, (-450639272359)⟩
theorem plane_0_1_4_eq : sourcePlane 0 1 4 = plane_0_1_4 := by rfl
theorem plane_0_1_4_sound (p : Point) (h : ClosedCell 1 (view 0 p)) :
    plane_0_1_4.rational.contains p := by
  rw [← plane_0_1_4_eq]
  exact sourcePlane_sound 0 1 4 p h

def plane_0_1_6 : IntegerPlane := ⟨2083356000000, 746024000000, 1117516707941⟩
theorem plane_0_1_6_eq : sourcePlane 0 1 6 = plane_0_1_6 := by rfl
theorem plane_0_1_6_sound (p : Point) (h : ClosedCell 1 (view 0 p)) :
    plane_0_1_6.rational.contains p := by
  rw [← plane_0_1_6_eq]
  exact sourcePlane_sound 0 1 6 p h

def plane_0_1_7 : IntegerPlane := ⟨3938876000000, 458408000000, 2473660467541⟩
theorem plane_0_1_7_eq : sourcePlane 0 1 7 = plane_0_1_7 := by rfl
theorem plane_0_1_7_sound (p : Point) (h : ClosedCell 1 (view 0 p)) :
    plane_0_1_7.rational.contains p := by
  rw [← plane_0_1_7_eq]
  exact sourcePlane_sound 0 1 7 p h

def plane_0_1_8 : IntegerPlane := ⟨(-2160892000000), 2839008000000, 118322956073⟩
theorem plane_0_1_8_eq : sourcePlane 0 1 8 = plane_0_1_8 := by rfl
theorem plane_0_1_8_sound (p : Point) (h : ClosedCell 1 (view 0 p)) :
    plane_0_1_8.rational.contains p := by
  rw [← plane_0_1_8_eq]
  exact sourcePlane_sound 0 1 8 p h

def plane_0_1_9 : IntegerPlane := ⟨(-16372000000), 2139440000000, 377332847425⟩
theorem plane_0_1_9_eq : sourcePlane 0 1 9 = plane_0_1_9 := by rfl
theorem plane_0_1_9_sound (p : Point) (h : ClosedCell 1 (view 0 p)) :
    plane_0_1_9.rational.contains p := by
  rw [← plane_0_1_9_eq]
  exact sourcePlane_sound 0 1 9 p h

def plane_0_2_2 : IntegerPlane := ⟨0, (-1), 0⟩
theorem plane_0_2_2_eq : sourcePlane 0 2 2 = plane_0_2_2 := by rfl
theorem plane_0_2_2_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_2.rational.contains p := by
  rw [← plane_0_2_2_eq]
  exact sourcePlane_sound 0 2 2 p h

def plane_0_2_4 : IntegerPlane := ⟨(-4229044000000), (-46700000000), (-1568155980300)⟩
theorem plane_0_2_4_eq : sourcePlane 0 2 4 = plane_0_2_4 := by rfl
theorem plane_0_2_4_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_4.rational.contains p := by
  rw [← plane_0_2_4_eq]
  exact sourcePlane_sound 0 2 4 p h

def plane_0_2_5 : IntegerPlane := ⟨(-2083356000000), (-746024000000), (-1117516707941)⟩
theorem plane_0_2_5_eq : sourcePlane 0 2 5 = plane_0_2_5 := by rfl
theorem plane_0_2_5_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_5.rational.contains p := by
  rw [← plane_0_2_5_eq]
  exact sourcePlane_sound 0 2 5 p h

def plane_0_2_7 : IntegerPlane := ⟨1855520000000, (-287616000000), 1356143759600⟩
theorem plane_0_2_7_eq : sourcePlane 0 2 7 = plane_0_2_7 := by rfl
theorem plane_0_2_7_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_7.rational.contains p := by
  rw [← plane_0_2_7_eq]
  exact sourcePlane_sound 0 2 7 p h

def plane_0_2_9 : IntegerPlane := ⟨(-2099728000000), 1393416000000, (-740183860516)⟩
theorem plane_0_2_9_eq : sourcePlane 0 2 9 = plane_0_2_9 := by rfl
theorem plane_0_2_9_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_9.rational.contains p := by
  rw [← plane_0_2_9_eq]
  exact sourcePlane_sound 0 2 9 p h

def plane_0_2_10 : IntegerPlane := ⟨13084000000, 2218132000000, 623586975028⟩
theorem plane_0_2_10_eq : sourcePlane 0 2 10 = plane_0_2_10 := by rfl
theorem plane_0_2_10_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_10.rational.contains p := by
  rw [← plane_0_2_10_eq]
  exact sourcePlane_sound 0 2 10 p h

def plane_0_2_11 : IntegerPlane := ⟨2058052000000, 1574160000000, 1942047499047⟩
theorem plane_0_2_11_eq : sourcePlane 0 2 11 = plane_0_2_11 := by rfl
theorem plane_0_2_11_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_11.rational.contains p := by
  rw [← plane_0_2_11_eq]
  exact sourcePlane_sound 0 2 11 p h

def plane_0_2_12 : IntegerPlane := ⟨(-4195996000000), 4205744000000, 130815499047⟩
theorem plane_0_2_12_eq : sourcePlane 0 2 12 = plane_0_2_12 := by rfl
theorem plane_0_2_12_sound (p : Point) (h : ClosedCell 2 (view 0 p)) :
    plane_0_2_12.rational.contains p := by
  rw [← plane_0_2_12_eq]
  exact sourcePlane_sound 0 2 12 p h

def plane_0_3_1 : IntegerPlane := ⟨1, 0, 1⟩
theorem plane_0_3_1_eq : sourcePlane 0 3 1 = plane_0_3_1 := by rfl
theorem plane_0_3_1_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_1.rational.contains p := by
  rw [← plane_0_3_1_eq]
  exact sourcePlane_sound 0 3 1 p h

def plane_0_3_2 : IntegerPlane := ⟨0, (-1), 0⟩
theorem plane_0_3_2_eq : sourcePlane 0 3 2 = plane_0_3_2 := by rfl
theorem plane_0_3_2_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_2.rational.contains p := by
  rw [← plane_0_3_2_eq]
  exact sourcePlane_sound 0 3 2 p h

def plane_0_3_5 : IntegerPlane := ⟨(-3938876000000), (-458408000000), (-2473660467541)⟩
theorem plane_0_3_5_eq : sourcePlane 0 3 5 = plane_0_3_5 := by rfl
theorem plane_0_3_5_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_5.rational.contains p := by
  rw [← plane_0_3_5_eq]
  exact sourcePlane_sound 0 3 5 p h

def plane_0_3_6 : IntegerPlane := ⟨(-1855520000000), 287616000000, (-1356143759600)⟩
theorem plane_0_3_6_eq : sourcePlane 0 3 6 = plane_0_3_6 := by rfl
theorem plane_0_3_6_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_6.rational.contains p := by
  rw [← plane_0_3_6_eq]
  exact sourcePlane_sound 0 3 6 p h

def plane_0_3_10 : IntegerPlane := ⟨(-1842436000000), 2505748000000, (-732556784572)⟩
theorem plane_0_3_10_eq : sourcePlane 0 3 10 = plane_0_3_10 := by rfl
theorem plane_0_3_10_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_10.rational.contains p := by
  rw [← plane_0_3_10_eq]
  exact sourcePlane_sound 0 3 10 p h

def plane_0_3_11 : IntegerPlane := ⟨202532000000, 1861776000000, 585903739447⟩
theorem plane_0_3_11_eq : sourcePlane 0 3 11 = plane_0_3_11 := by rfl
theorem plane_0_3_11_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_11.rational.contains p := by
  rw [← plane_0_3_11_eq]
  exact sourcePlane_sound 0 3 11 p h

def plane_0_3_14 : IntegerPlane := ⟨(-1893736000000), 4674104000000, 430964379884⟩
theorem plane_0_3_14_eq : sourcePlane 0 3 14 = plane_0_3_14 := by rfl
theorem plane_0_3_14_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_14.rational.contains p := by
  rw [← plane_0_3_14_eq]
  exact sourcePlane_sound 0 3 14 p h

def plane_0_3_16 : IntegerPlane := ⟨(-5848984000000), 6355136000000, 253076000000⟩
theorem plane_0_3_16_eq : sourcePlane 0 3 16 = plane_0_3_16 := by rfl
theorem plane_0_3_16_sound (p : Point) (h : ClosedCell 3 (view 0 p)) :
    plane_0_3_16.rational.contains p := by
  rw [← plane_0_3_16_eq]
  exact sourcePlane_sound 0 3 16 p h

def plane_0_4_0 : IntegerPlane := ⟨(-1), 0, 0⟩
theorem plane_0_4_0_eq : sourcePlane 0 4 0 = plane_0_4_0 := by rfl
theorem plane_0_4_0_sound (p : Point) (h : ClosedCell 4 (view 0 p)) :
    plane_0_4_0.rational.contains p := by
  rw [← plane_0_4_0_eq]
  exact sourcePlane_sound 0 4 0 p h

def plane_0_4_4 : IntegerPlane := ⟨15204000000, (-2139684000000), (-568962228432)⟩
theorem plane_0_4_4_eq : sourcePlane 0 4 4 = plane_0_4_4 := by rfl
theorem plane_0_4_4_sound (p : Point) (h : ClosedCell 4 (view 0 p)) :
    plane_0_4_4.rational.contains p := by
  rw [← plane_0_4_4_eq]
  exact sourcePlane_sound 0 4 4 p h

def plane_0_4_5 : IntegerPlane := ⟨2160892000000, (-2839008000000), (-118322956073)⟩
theorem plane_0_4_5_eq : sourcePlane 0 4 5 = plane_0_4_5 := by rfl
theorem plane_0_4_5_sound (p : Point) (h : ClosedCell 4 (view 0 p)) :
    plane_0_4_5.rational.contains p := by
  rw [← plane_0_4_5_eq]
  exact sourcePlane_sound 0 4 5 p h

def plane_0_4_9 : IntegerPlane := ⟨2144520000000, (-699568000000), 259009891352⟩
theorem plane_0_4_9_eq : sourcePlane 0 4 9 = plane_0_4_9 := by rfl
theorem plane_0_4_9_sound (p : Point) (h : ClosedCell 4 (view 0 p)) :
    plane_0_4_9.rational.contains p := by
  rw [← plane_0_4_9_eq]
  exact sourcePlane_sound 0 4 9 p h

def plane_0_4_10 : IntegerPlane := ⟨4257332000000, 125148000000, 1622780726896⟩
theorem plane_0_4_10_eq : sourcePlane 0 4 10 = plane_0_4_10 := by rfl
theorem plane_0_4_10_sound (p : Point) (h : ClosedCell 4 (view 0 p)) :
    plane_0_4_10.rational.contains p := by
  rw [← plane_0_4_10_eq]
  exact sourcePlane_sound 0 4 10 p h

def plane_0_4_12 : IntegerPlane := ⟨48252000000, 2112760000000, 1130009250915⟩
theorem plane_0_4_12_eq : sourcePlane 0 4 12 = plane_0_4_12 := by rfl
theorem plane_0_4_12_sound (p : Point) (h : ClosedCell 4 (view 0 p)) :
    plane_0_4_12.rational.contains p := by
  rw [← plane_0_4_12_eq]
  exact sourcePlane_sound 0 4 12 p h

def plane_0_4_13 : IntegerPlane := ⟨2093220000000, 1468788000000, 1212544726896⟩
theorem plane_0_4_13_eq : sourcePlane 0 4 13 = plane_0_4_13 := by rfl
theorem plane_0_4_13_sound (p : Point) (h : ClosedCell 4 (view 0 p)) :
    plane_0_4_13.rational.contains p := by
  rw [← plane_0_4_13_eq]
  exact sourcePlane_sound 0 4 13 p h

def plane_0_5_4 : IntegerPlane := ⟨(-2129316000000), (-1440116000000), (-827972119784)⟩
theorem plane_0_5_4_eq : sourcePlane 0 5 4 = plane_0_5_4 := by rfl
theorem plane_0_5_4_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_4.rational.contains p := by
  rw [← plane_0_5_4_eq]
  exact sourcePlane_sound 0 5 4 p h

def plane_0_5_5 : IntegerPlane := ⟨16372000000, (-2139440000000), (-377332847425)⟩
theorem plane_0_5_5_eq : sourcePlane 0 5 5 = plane_0_5_5 := by rfl
theorem plane_0_5_5_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_5.rational.contains p := by
  rw [← plane_0_5_5_eq]
  exact sourcePlane_sound 0 5 5 p h

def plane_0_5_6 : IntegerPlane := ⟨2099728000000, (-1393416000000), 740183860516⟩
theorem plane_0_5_6_eq : sourcePlane 0 5 6 = plane_0_5_6 := by rfl
theorem plane_0_5_6_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_6.rational.contains p := by
  rw [← plane_0_5_6_eq]
  exact sourcePlane_sound 0 5 6 p h

def plane_0_5_8 : IntegerPlane := ⟨(-2144520000000), 699568000000, (-259009891352)⟩
theorem plane_0_5_8_eq : sourcePlane 0 5 8 = plane_0_5_8 := by rfl
theorem plane_0_5_8_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_8.rational.contains p := by
  rw [← plane_0_5_8_eq]
  exact sourcePlane_sound 0 5 8 p h

def plane_0_5_10 : IntegerPlane := ⟨2112812000000, 824716000000, 1363770835544⟩
theorem plane_0_5_10_eq : sourcePlane 0 5 10 = plane_0_5_10 := by rfl
theorem plane_0_5_10_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_10.rational.contains p := by
  rw [← plane_0_5_10_eq]
  exact sourcePlane_sound 0 5 10 p h

def plane_0_5_11 : IntegerPlane := ⟨4157780000000, 180744000000, 2682231359563⟩
theorem plane_0_5_11_eq : sourcePlane 0 5 11 = plane_0_5_11 := by rfl
theorem plane_0_5_11_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_11.rational.contains p := by
  rw [← plane_0_5_11_eq]
  exact sourcePlane_sound 0 5 11 p h

def plane_0_5_13 : IntegerPlane := ⟨(-51300000000), 2168356000000, 953534835544⟩
theorem plane_0_5_13_eq : sourcePlane 0 5 13 = plane_0_5_13 := by rfl
theorem plane_0_5_13_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_13.rational.contains p := by
  rw [← plane_0_5_13_eq]
  exact sourcePlane_sound 0 5 13 p h

def plane_0_5_17 : IntegerPlane := ⟨(-38216000000), 4386488000000, 2561163860516⟩
theorem plane_0_5_17_eq : sourcePlane 0 5 17 = plane_0_5_17 := by rfl
theorem plane_0_5_17_sound (p : Point) (h : ClosedCell 5 (view 0 p)) :
    plane_0_5_17.rational.contains p := by
  rw [← plane_0_5_17_eq]
  exact sourcePlane_sound 0 5 17 p h

def plane_0_6_6 : IntegerPlane := ⟨(-13084000000), (-2218132000000), (-623586975028)⟩
theorem plane_0_6_6_eq : sourcePlane 0 6 6 = plane_0_6_6 := by rfl
theorem plane_0_6_6_sound (p : Point) (h : ClosedCell 6 (view 0 p)) :
    plane_0_6_6.rational.contains p := by
  rw [← plane_0_6_6_eq]
  exact sourcePlane_sound 0 6 6 p h

def plane_0_6_8 : IntegerPlane := ⟨(-4257332000000), (-125148000000), (-1622780726896)⟩
theorem plane_0_6_8_eq : sourcePlane 0 6 8 = plane_0_6_8 := by rfl
theorem plane_0_6_8_sound (p : Point) (h : ClosedCell 6 (view 0 p)) :
    plane_0_6_8.rational.contains p := by
  rw [← plane_0_6_8_eq]
  exact sourcePlane_sound 0 6 8 p h

def plane_0_6_9 : IntegerPlane := ⟨(-2112812000000), (-824716000000), (-1363770835544)⟩
theorem plane_0_6_9_eq : sourcePlane 0 6 9 = plane_0_6_9 := by rfl
theorem plane_0_6_9_sound (p : Point) (h : ClosedCell 6 (view 0 p)) :
    plane_0_6_9.rational.contains p := by
  rw [← plane_0_6_9_eq]
  exact sourcePlane_sound 0 6 9 p h

def plane_0_6_11 : IntegerPlane := ⟨2044968000000, (-643972000000), 1318460524019⟩
theorem plane_0_6_11_eq : sourcePlane 0 6 11 = plane_0_6_11 := by rfl
theorem plane_0_6_11_sound (p : Point) (h : ClosedCell 6 (view 0 p)) :
    plane_0_6_11.rational.contains p := by
  rw [← plane_0_6_11_eq]
  exact sourcePlane_sound 0 6 11 p h

def plane_0_6_13 : IntegerPlane := ⟨(-2164112000000), 1343640000000, (-410236000000)⟩
theorem plane_0_6_13_eq : sourcePlane 0 6 13 = plane_0_6_13 := by rfl
theorem plane_0_6_13_sound (p : Point) (h : ClosedCell 6 (view 0 p)) :
    plane_0_6_13.rational.contains p := by
  rw [← plane_0_6_13_eq]
  exact sourcePlane_sound 0 6 13 p h

def plane_0_6_14 : IntegerPlane := ⟨(-51300000000), 2168356000000, 1163521164456⟩
theorem plane_0_6_14_eq : sourcePlane 0 6 14 = plane_0_6_14 := by rfl
theorem plane_0_6_14_sound (p : Point) (h : ClosedCell 6 (view 0 p)) :
    plane_0_6_14.rational.contains p := by
  rw [← plane_0_6_14_eq]
  exact sourcePlane_sound 0 6 14 p h

def plane_0_6_15 : IntegerPlane := ⟨2093220000000, 1468788000000, 2349463273104⟩
theorem plane_0_6_15_eq : sourcePlane 0 6 15 = plane_0_6_15 := by rfl
theorem plane_0_6_15_sound (p : Point) (h : ClosedCell 6 (view 0 p)) :
    plane_0_6_15.rational.contains p := by
  rw [← plane_0_6_15_eq]
  exact sourcePlane_sound 0 6 15 p h

def plane_0_7_1 : IntegerPlane := ⟨1, 0, 1⟩
theorem plane_0_7_1_eq : sourcePlane 0 7 1 = plane_0_7_1 := by rfl
theorem plane_0_7_1_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_1.rational.contains p := by
  rw [← plane_0_7_1_eq]
  exact sourcePlane_sound 0 7 1 p h

def plane_0_7_7 : IntegerPlane := ⟨(-202532000000), (-1861776000000), (-585903739447)⟩
theorem plane_0_7_7_eq : sourcePlane 0 7 7 = plane_0_7_7 := by rfl
theorem plane_0_7_7_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_7.rational.contains p := by
  rw [← plane_0_7_7_eq]
  exact sourcePlane_sound 0 7 7 p h

def plane_0_7_9 : IntegerPlane := ⟨(-4157780000000), (-180744000000), (-2682231359563)⟩
theorem plane_0_7_9_eq : sourcePlane 0 7 9 = plane_0_7_9 := by rfl
theorem plane_0_7_9_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_9.rational.contains p := by
  rw [← plane_0_7_9_eq]
  exact sourcePlane_sound 0 7 9 p h

def plane_0_7_10 : IntegerPlane := ⟨(-2044968000000), 643972000000, (-1318460524019)⟩
theorem plane_0_7_10_eq : sourcePlane 0 7 10 = plane_0_7_10 := by rfl
theorem plane_0_7_10_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_10.rational.contains p := by
  rw [← plane_0_7_10_eq]
  exact sourcePlane_sound 0 7 10 p h

def plane_0_7_14 : IntegerPlane := ⟨(-2096268000000), 2812328000000, (-154939359563)⟩
theorem plane_0_7_14_eq : sourcePlane 0 7 14 = plane_0_7_14 := by rfl
theorem plane_0_7_14_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_14.rational.contains p := by
  rw [← plane_0_7_14_eq]
  exact sourcePlane_sound 0 7 14 p h

def plane_0_7_15 : IntegerPlane := ⟨48252000000, 2112760000000, 1031002749085⟩
theorem plane_0_7_15_eq : sourcePlane 0 7 15 = plane_0_7_15 := by rfl
theorem plane_0_7_15_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_15.rational.contains p := by
  rw [← plane_0_7_15_eq]
  exact sourcePlane_sound 0 7 15 p h

def plane_0_7_17 : IntegerPlane := ⟨(-4195996000000), 4205744000000, (-121067499047)⟩
theorem plane_0_7_17_eq : sourcePlane 0 7 17 = plane_0_7_17 := by rfl
theorem plane_0_7_17_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_17.rational.contains p := by
  rw [← plane_0_7_17_eq]
  exact sourcePlane_sound 0 7 17 p h

def plane_0_7_19 : IntegerPlane := ⟨33048000000, 4252444000000, 2586520520653⟩
theorem plane_0_7_19_eq : sourcePlane 0 7 19 = plane_0_7_19 := by rfl
theorem plane_0_7_19_sound (p : Point) (h : ClosedCell 7 (view 0 p)) :
    plane_0_7_19.rational.contains p := by
  rw [← plane_0_7_19_eq]
  exact sourcePlane_sound 0 7 19 p h

def plane_0_8_0 : IntegerPlane := ⟨(-1), 0, 0⟩
theorem plane_0_8_0_eq : sourcePlane 0 8 0 = plane_0_8_0 := by rfl
theorem plane_0_8_0_sound (p : Point) (h : ClosedCell 8 (view 0 p)) :
    plane_0_8_0.rational.contains p := by
  rw [← plane_0_8_0_eq]
  exact sourcePlane_sound 0 8 0 p h

def plane_0_8_4 : IntegerPlane := ⟨(-33048000000), (-4252444000000), (-1698971479347)⟩
theorem plane_0_8_4_eq : sourcePlane 0 8 4 = plane_0_8_4 := by rfl
theorem plane_0_8_4_sound (p : Point) (h : ClosedCell 8 (view 0 p)) :
    plane_0_8_4.rational.contains p := by
  rw [← plane_0_8_4_eq]
  exact sourcePlane_sound 0 8 4 p h

def plane_0_8_6 : IntegerPlane := ⟨4195996000000, (-4205744000000), (-130815499047)⟩
theorem plane_0_8_6_eq : sourcePlane 0 8 6 = plane_0_8_6 := by rfl
theorem plane_0_8_6_sound (p : Point) (h : ClosedCell 8 (view 0 p)) :
    plane_0_8_6.rational.contains p := by
  rw [← plane_0_8_6_eq]
  exact sourcePlane_sound 0 8 6 p h

def plane_0_8_8 : IntegerPlane := ⟨(-48252000000), (-2112760000000), (-1130009250915)⟩
theorem plane_0_8_8_eq : sourcePlane 0 8 8 = plane_0_8_8 := by rfl
theorem plane_0_8_8_sound (p : Point) (h : ClosedCell 8 (view 0 p)) :
    plane_0_8_8.rational.contains p := by
  rw [← plane_0_8_8_eq]
  exact sourcePlane_sound 0 8 8 p h

def plane_0_8_13 : IntegerPlane := ⟨2044968000000, (-643972000000), 82535475981⟩
theorem plane_0_8_13_eq : sourcePlane 0 8 13 = plane_0_8_13 := by rfl
theorem plane_0_8_13_sound (p : Point) (h : ClosedCell 8 (view 0 p)) :
    plane_0_8_13.rational.contains p := by
  rw [← plane_0_8_13_eq]
  exact sourcePlane_sound 0 8 13 p h

def plane_0_8_16 : IntegerPlane := ⟨202532000000, 1861776000000, 1478404260553⟩
theorem plane_0_8_16_eq : sourcePlane 0 8 16 = plane_0_8_16 := by rfl
theorem plane_0_8_16_sound (p : Point) (h : ClosedCell 8 (view 0 p)) :
    plane_0_8_16.rational.contains p := by
  rw [← plane_0_8_16_eq]
  exact sourcePlane_sound 0 8 16 p h

def plane_0_9_8 : IntegerPlane := ⟨(-2093220000000), (-1468788000000), (-1212544726896)⟩
theorem plane_0_9_8_eq : sourcePlane 0 9 8 = plane_0_9_8 := by rfl
theorem plane_0_9_8_sound (p : Point) (h : ClosedCell 9 (view 0 p)) :
    plane_0_9_8.rational.contains p := by
  rw [← plane_0_9_8_eq]
  exact sourcePlane_sound 0 9 8 p h

def plane_0_9_9 : IntegerPlane := ⟨51300000000, (-2168356000000), (-953534835544)⟩
theorem plane_0_9_9_eq : sourcePlane 0 9 9 = plane_0_9_9 := by rfl
theorem plane_0_9_9_sound (p : Point) (h : ClosedCell 9 (view 0 p)) :
    plane_0_9_9.rational.contains p := by
  rw [← plane_0_9_9_eq]
  exact sourcePlane_sound 0 9 9 p h

def plane_0_9_10 : IntegerPlane := ⟨2164112000000, (-1343640000000), 410236000000⟩
theorem plane_0_9_10_eq : sourcePlane 0 9 10 = plane_0_9_10 := by rfl
theorem plane_0_9_10_sound (p : Point) (h : ClosedCell 9 (view 0 p)) :
    plane_0_9_10.rational.contains p := by
  rw [← plane_0_9_10_eq]
  exact sourcePlane_sound 0 9 10 p h

def plane_0_9_12 : IntegerPlane := ⟨(-2044968000000), 643972000000, (-82535475981)⟩
theorem plane_0_9_12_eq : sourcePlane 0 9 12 = plane_0_9_12 := by rfl
theorem plane_0_9_12_sound (p : Point) (h : ClosedCell 9 (view 0 p)) :
    plane_0_9_12.rational.contains p := by
  rw [← plane_0_9_12_eq]
  exact sourcePlane_sound 0 9 12 p h

def plane_0_9_14 : IntegerPlane := ⟨2112812000000, 824716000000, 1573757164456⟩
theorem plane_0_9_14_eq : sourcePlane 0 9 14 = plane_0_9_14 := by rfl
theorem plane_0_9_14_sound (p : Point) (h : ClosedCell 9 (view 0 p)) :
    plane_0_9_14.rational.contains p := by
  rw [← plane_0_9_14_eq]
  exact sourcePlane_sound 0 9 14 p h

def plane_0_9_15 : IntegerPlane := ⟨4257332000000, 125148000000, 2759699273104⟩
theorem plane_0_9_15_eq : sourcePlane 0 9 15 = plane_0_9_15 := by rfl
theorem plane_0_9_15_sound (p : Point) (h : ClosedCell 9 (view 0 p)) :
    plane_0_9_15.rational.contains p := by
  rw [← plane_0_9_15_eq]
  exact sourcePlane_sound 0 9 15 p h

def plane_0_9_17 : IntegerPlane := ⟨13084000000, 2218132000000, 1607629024972⟩
theorem plane_0_9_17_eq : sourcePlane 0 9 17 = plane_0_9_17 := by rfl
theorem plane_0_9_17_sound (p : Point) (h : ClosedCell 9 (view 0 p)) :
    plane_0_9_17.rational.contains p := by
  rw [← plane_0_9_17_eq]
  exact sourcePlane_sound 0 9 17 p h

def plane_0_10_6 : IntegerPlane := ⟨38216000000, (-4386488000000), (-1787108139484)⟩
theorem plane_0_10_6_eq : sourcePlane 0 10 6 = plane_0_10_6 := by rfl
theorem plane_0_10_6_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_6.rational.contains p := by
  rw [← plane_0_10_6_eq]
  exact sourcePlane_sound 0 10 6 p h

def plane_0_10_10 : IntegerPlane := ⟨51300000000, (-2168356000000), (-1163521164456)⟩
theorem plane_0_10_10_eq : sourcePlane 0 10 10 = plane_0_10_10 := by rfl
theorem plane_0_10_10_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_10.rational.contains p := by
  rw [← plane_0_10_10_eq]
  exact sourcePlane_sound 0 10 10 p h

def plane_0_10_11 : IntegerPlane := ⟨2096268000000, (-2812328000000), 154939359563⟩
theorem plane_0_10_11_eq : sourcePlane 0 10 11 = plane_0_10_11 := by rfl
theorem plane_0_10_11_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_11.rational.contains p := by
  rw [← plane_0_10_11_eq]
  exact sourcePlane_sound 0 10 11 p h

def plane_0_10_12 : IntegerPlane := ⟨(-4157780000000), (-180744000000), (-1656292640437)⟩
theorem plane_0_10_12_eq : sourcePlane 0 10 12 = plane_0_10_12 := by rfl
theorem plane_0_10_12_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_12.rational.contains p := by
  rw [← plane_0_10_12_eq]
  exact sourcePlane_sound 0 10 12 p h

def plane_0_10_13 : IntegerPlane := ⟨(-2112812000000), (-824716000000), (-1573757164456)⟩
theorem plane_0_10_13_eq : sourcePlane 0 10 13 = plane_0_10_13 := by rfl
theorem plane_0_10_13_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_13.rational.contains p := by
  rw [← plane_0_10_13_eq]
  exact sourcePlane_sound 0 10 13 p h

def plane_0_10_15 : IntegerPlane := ⟨2144520000000, (-699568000000), 1185942108648⟩
theorem plane_0_10_15_eq : sourcePlane 0 10 15 = plane_0_10_15 := by rfl
theorem plane_0_10_15_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_15.rational.contains p := by
  rw [← plane_0_10_15_eq]
  exact sourcePlane_sound 0 10 15 p h

def plane_0_10_17 : IntegerPlane := ⟨(-2099728000000), 1393416000000, 33871860516⟩
theorem plane_0_10_17_eq : sourcePlane 0 10 17 = plane_0_10_17 := by rfl
theorem plane_0_10_17_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_17.rational.contains p := by
  rw [← plane_0_10_17_eq]
  exact sourcePlane_sound 0 10 17 p h

def plane_0_10_18 : IntegerPlane := ⟨(-16372000000), 2139440000000, 1745735152575⟩
theorem plane_0_10_18_eq : sourcePlane 0 10 18 = plane_0_10_18 := by rfl
theorem plane_0_10_18_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_18.rational.contains p := by
  rw [← plane_0_10_18_eq]
  exact sourcePlane_sound 0 10 18 p h

def plane_0_10_19 : IntegerPlane := ⟨2129316000000, 1440116000000, 2741459880216⟩
theorem plane_0_10_19_eq : sourcePlane 0 10 19 = plane_0_10_19 := by rfl
theorem plane_0_10_19_sound (p : Point) (h : ClosedCell 10 (view 0 p)) :
    plane_0_10_19.rational.contains p := by
  rw [← plane_0_10_19_eq]
  exact sourcePlane_sound 0 10 19 p h

def plane_0_11_1 : IntegerPlane := ⟨1, 0, 1⟩
theorem plane_0_11_1_eq : sourcePlane 0 11 1 = plane_0_11_1 := by rfl
theorem plane_0_11_1_sound (p : Point) (h : ClosedCell 11 (view 0 p)) :
    plane_0_11_1.rational.contains p := by
  rw [← plane_0_11_1_eq]
  exact sourcePlane_sound 0 11 1 p h

def plane_0_11_10 : IntegerPlane := ⟨(-2093220000000), (-1468788000000), (-2349463273104)⟩
theorem plane_0_11_10_eq : sourcePlane 0 11 10 = plane_0_11_10 := by rfl
theorem plane_0_11_10_sound (p : Point) (h : ClosedCell 11 (view 0 p)) :
    plane_0_11_10.rational.contains p := by
  rw [← plane_0_11_10_eq]
  exact sourcePlane_sound 0 11 10 p h

def plane_0_11_11 : IntegerPlane := ⟨(-48252000000), (-2112760000000), (-1031002749085)⟩
theorem plane_0_11_11_eq : sourcePlane 0 11 11 = plane_0_11_11 := by rfl
theorem plane_0_11_11_sound (p : Point) (h : ClosedCell 11 (view 0 p)) :
    plane_0_11_11.rational.contains p := by
  rw [← plane_0_11_11_eq]
  exact sourcePlane_sound 0 11 11 p h

def plane_0_11_13 : IntegerPlane := ⟨(-4257332000000), (-125148000000), (-2759699273104)⟩
theorem plane_0_11_13_eq : sourcePlane 0 11 13 = plane_0_11_13 := by rfl
theorem plane_0_11_13_sound (p : Point) (h : ClosedCell 11 (view 0 p)) :
    plane_0_11_13.rational.contains p := by
  rw [← plane_0_11_13_eq]
  exact sourcePlane_sound 0 11 13 p h

def plane_0_11_14 : IntegerPlane := ⟨(-2144520000000), 699568000000, (-1185942108648)⟩
theorem plane_0_11_14_eq : sourcePlane 0 11 14 = plane_0_11_14 := by rfl
theorem plane_0_11_14_sound (p : Point) (h : ClosedCell 11 (view 0 p)) :
    plane_0_11_14.rational.contains p := by
  rw [← plane_0_11_14_eq]
  exact sourcePlane_sound 0 11 14 p h

def plane_0_11_19 : IntegerPlane := ⟨(-15204000000), 2139684000000, 1555517771568⟩
theorem plane_0_11_19_eq : sourcePlane 0 11 19 = plane_0_11_19 := by rfl
theorem plane_0_11_19_sound (p : Point) (h : ClosedCell 11 (view 0 p)) :
    plane_0_11_19.rational.contains p := by
  rw [← plane_0_11_19_eq]
  exact sourcePlane_sound 0 11 19 p h

def plane_0_12_0 : IntegerPlane := ⟨(-1), 0, 0⟩
theorem plane_0_12_0_eq : sourcePlane 0 12 0 = plane_0_12_0 := by rfl
theorem plane_0_12_0_sound (p : Point) (h : ClosedCell 12 (view 0 p)) :
    plane_0_12_0.rational.contains p := by
  rw [← plane_0_12_0_eq]
  exact sourcePlane_sound 0 12 0 p h

def plane_0_12_3 : IntegerPlane := ⟨0, 1, 1⟩
theorem plane_0_12_3_eq : sourcePlane 0 12 3 = plane_0_12_3 := by rfl
theorem plane_0_12_3_sound (p : Point) (h : ClosedCell 12 (view 0 p)) :
    plane_0_12_3.rational.contains p := by
  rw [← plane_0_12_3_eq]
  exact sourcePlane_sound 0 12 3 p h

def plane_0_12_8 : IntegerPlane := ⟨(-250784000000), (-3974536000000), (-2608413511468)⟩
theorem plane_0_12_8_eq : sourcePlane 0 12 8 = plane_0_12_8 := by rfl
theorem plane_0_12_8_sound (p : Point) (h : ClosedCell 12 (view 0 p)) :
    plane_0_12_8.rational.contains p := by
  rw [← plane_0_12_8_eq]
  exact sourcePlane_sound 0 12 8 p h

def plane_0_12_12 : IntegerPlane := ⟨(-202532000000), (-1861776000000), (-1478404260553)⟩
theorem plane_0_12_12_eq : sourcePlane 0 12 12 = plane_0_12_12 := by rfl
theorem plane_0_12_12_sound (p : Point) (h : ClosedCell 12 (view 0 p)) :
    plane_0_12_12.rational.contains p := by
  rw [← plane_0_12_12_eq]
  exact sourcePlane_sound 0 12 12 p h

def plane_0_12_14 : IntegerPlane := ⟨3955248000000, (-1681032000000), 177888379884⟩
theorem plane_0_12_14_eq : sourcePlane 0 12 14 = plane_0_12_14 := by rfl
theorem plane_0_12_14_sound (p : Point) (h : ClosedCell 12 (view 0 p)) :
    plane_0_12_14.rational.contains p := by
  rw [← plane_0_12_14_eq]
  exact sourcePlane_sound 0 12 14 p h

def plane_0_12_17 : IntegerPlane := ⟨1855520000000, (-287616000000), 211760240400⟩
theorem plane_0_12_17_eq : sourcePlane 0 12 17 = plane_0_12_17 := by rfl
theorem plane_0_12_17_sound (p : Point) (h : ClosedCell 12 (view 0 p)) :
    plane_0_12_17.rational.contains p := by
  rw [← plane_0_12_17_eq]
  exact sourcePlane_sound 0 12 17 p h

def plane_0_12_18 : IntegerPlane := ⟨3938876000000, 458408000000, 1923623532459⟩
theorem plane_0_12_18_eq : sourcePlane 0 12 18 = plane_0_12_18 := by rfl
theorem plane_0_12_18_sound (p : Point) (h : ClosedCell 12 (view 0 p)) :
    plane_0_12_18.rational.contains p := by
  rw [← plane_0_12_18_eq]
  exact sourcePlane_sound 0 12 18 p h

def plane_0_13_3 : IntegerPlane := ⟨0, 1, 1⟩
theorem plane_0_13_3_eq : sourcePlane 0 13 3 = plane_0_13_3 := by rfl
theorem plane_0_13_3_sound (p : Point) (h : ClosedCell 13 (view 0 p)) :
    plane_0_13_3.rational.contains p := by
  rw [← plane_0_13_3_eq]
  exact sourcePlane_sound 0 13 3 p h

def plane_0_13_12 : IntegerPlane := ⟨(-2058052000000), (-1574160000000), (-1690164500953)⟩
theorem plane_0_13_12_eq : sourcePlane 0 13 12 = plane_0_13_12 := by rfl
theorem plane_0_13_12_sound (p : Point) (h : ClosedCell 13 (view 0 p)) :
    plane_0_13_12.rational.contains p := by
  rw [← plane_0_13_12_eq]
  exact sourcePlane_sound 0 13 12 p h

def plane_0_13_13 : IntegerPlane := ⟨(-13084000000), (-2218132000000), (-1607629024972)⟩
theorem plane_0_13_13_eq : sourcePlane 0 13 13 = plane_0_13_13 := by rfl
theorem plane_0_13_13_sound (p : Point) (h : ClosedCell 13 (view 0 p)) :
    plane_0_13_13.rational.contains p := by
  rw [← plane_0_13_13_eq]
  exact sourcePlane_sound 0 13 13 p h

def plane_0_13_14 : IntegerPlane := ⟨2099728000000, (-1393416000000), (-33871860516)⟩
theorem plane_0_13_14_eq : sourcePlane 0 13 14 = plane_0_13_14 := by rfl
theorem plane_0_13_14_sound (p : Point) (h : ClosedCell 13 (view 0 p)) :
    plane_0_13_14.rational.contains p := by
  rw [← plane_0_13_14_eq]
  exact sourcePlane_sound 0 13 14 p h

def plane_0_13_16 : IntegerPlane := ⟨(-1855520000000), 287616000000, (-211760240400)⟩
theorem plane_0_13_16_eq : sourcePlane 0 13 16 = plane_0_13_16 := by rfl
theorem plane_0_13_16_sound (p : Point) (h : ClosedCell 13 (view 0 p)) :
    plane_0_13_16.rational.contains p := by
  rw [← plane_0_13_16_eq]
  exact sourcePlane_sound 0 13 16 p h

def plane_0_13_18 : IntegerPlane := ⟨2083356000000, 746024000000, 1711863292059⟩
theorem plane_0_13_18_eq : sourcePlane 0 13 18 = plane_0_13_18 := by rfl
theorem plane_0_13_18_sound (p : Point) (h : ClosedCell 13 (view 0 p)) :
    plane_0_13_18.rational.contains p := by
  rw [← plane_0_13_18_eq]
  exact sourcePlane_sound 0 13 18 p h

def plane_0_13_19 : IntegerPlane := ⟨4229044000000, 46700000000, 2707588019700⟩
theorem plane_0_13_19_eq : sourcePlane 0 13 19 = plane_0_13_19 := by rfl
theorem plane_0_13_19_sound (p : Point) (h : ClosedCell 13 (view 0 p)) :
    plane_0_13_19.rational.contains p := by
  rw [← plane_0_13_19_eq]
  exact sourcePlane_sound 0 13 19 p h

def plane_0_14_3 : IntegerPlane := ⟨0, 1, 1⟩
theorem plane_0_14_3_eq : sourcePlane 0 14 3 = plane_0_14_3 := by rfl
theorem plane_0_14_3_sound (p : Point) (h : ClosedCell 14 (view 0 p)) :
    plane_0_14_3.rational.contains p := by
  rw [← plane_0_14_3_eq]
  exact sourcePlane_sound 0 14 3 p h

def plane_0_14_14 : IntegerPlane := ⟨16372000000, (-2139440000000), (-1745735152575)⟩
theorem plane_0_14_14_eq : sourcePlane 0 14 14 = plane_0_14_14 := by rfl
theorem plane_0_14_14_sound (p : Point) (h : ClosedCell 14 (view 0 p)) :
    plane_0_14_14.rational.contains p := by
  rw [← plane_0_14_14_eq]
  exact sourcePlane_sound 0 14 14 p h

def plane_0_14_15 : IntegerPlane := ⟨2160892000000, (-2839008000000), (-559793043927)⟩
theorem plane_0_14_15_eq : sourcePlane 0 14 15 = plane_0_14_15 := by rfl
theorem plane_0_14_15_sound (p : Point) (h : ClosedCell 14 (view 0 p)) :
    plane_0_14_15.rational.contains p := by
  rw [← plane_0_14_15_eq]
  exact sourcePlane_sound 0 14 15 p h

def plane_0_14_16 : IntegerPlane := ⟨(-3938876000000), (-458408000000), (-1923623532459)⟩
theorem plane_0_14_16_eq : sourcePlane 0 14 16 = plane_0_14_16 := by rfl
theorem plane_0_14_16_sound (p : Point) (h : ClosedCell 14 (view 0 p)) :
    plane_0_14_16.rational.contains p := by
  rw [← plane_0_14_16_eq]
  exact sourcePlane_sound 0 14 16 p h

def plane_0_14_17 : IntegerPlane := ⟨(-2083356000000), (-746024000000), (-1711863292059)⟩
theorem plane_0_14_17_eq : sourcePlane 0 14 17 = plane_0_14_17 := by rfl
theorem plane_0_14_17_sound (p : Point) (h : ClosedCell 14 (view 0 p)) :
    plane_0_14_17.rational.contains p := by
  rw [← plane_0_14_17_eq]
  exact sourcePlane_sound 0 14 17 p h

def plane_0_14_19 : IntegerPlane := ⟨2145688000000, (-699324000000), 995724727641⟩
theorem plane_0_14_19_eq : sourcePlane 0 14 19 = plane_0_14_19 := by rfl
theorem plane_0_14_19_sound (p : Point) (h : ClosedCell 14 (view 0 p)) :
    plane_0_14_19.rational.contains p := by
  rw [← plane_0_14_19_eq]
  exact sourcePlane_sound 0 14 19 p h

def plane_0_15_1 : IntegerPlane := ⟨1, 0, 1⟩
theorem plane_0_15_1_eq : sourcePlane 0 15 1 = plane_0_15_1 := by rfl
theorem plane_0_15_1_sound (p : Point) (h : ClosedCell 15 (view 0 p)) :
    plane_0_15_1.rational.contains p := by
  rw [← plane_0_15_1_eq]
  exact sourcePlane_sound 0 15 1 p h

def plane_0_15_3 : IntegerPlane := ⟨0, 1, 1⟩
theorem plane_0_15_3_eq : sourcePlane 0 15 3 = plane_0_15_3 := by rfl
theorem plane_0_15_3_sound (p : Point) (h : ClosedCell 15 (view 0 p)) :
    plane_0_15_3.rational.contains p := by
  rw [← plane_0_15_3_eq]
  exact sourcePlane_sound 0 15 3 p h

def plane_0_15_14 : IntegerPlane := ⟨(-2129316000000), (-1440116000000), (-2741459880216)⟩
theorem plane_0_15_14_eq : sourcePlane 0 15 14 = plane_0_15_14 := by rfl
theorem plane_0_15_14_sound (p : Point) (h : ClosedCell 15 (view 0 p)) :
    plane_0_15_14.rational.contains p := by
  rw [← plane_0_15_14_eq]
  exact sourcePlane_sound 0 15 14 p h

def plane_0_15_15 : IntegerPlane := ⟨15204000000, (-2139684000000), (-1555517771568)⟩
theorem plane_0_15_15_eq : sourcePlane 0 15 15 = plane_0_15_15 := by rfl
theorem plane_0_15_15_sound (p : Point) (h : ClosedCell 15 (view 0 p)) :
    plane_0_15_15.rational.contains p := by
  rw [← plane_0_15_15_eq]
  exact sourcePlane_sound 0 15 15 p h

def plane_0_15_17 : IntegerPlane := ⟨(-4229044000000), (-46700000000), (-2707588019700)⟩
theorem plane_0_15_17_eq : sourcePlane 0 15 17 = plane_0_15_17 := by rfl
theorem plane_0_15_17_sound (p : Point) (h : ClosedCell 15 (view 0 p)) :
    plane_0_15_17.rational.contains p := by
  rw [← plane_0_15_17_eq]
  exact sourcePlane_sound 0 15 17 p h

def plane_0_15_18 : IntegerPlane := ⟨(-2145688000000), 699324000000, (-995724727641)⟩
theorem plane_0_15_18_eq : sourcePlane 0 15 18 = plane_0_15_18 := by rfl
theorem plane_0_15_18_sound (p : Point) (h : ClosedCell 15 (view 0 p)) :
    plane_0_15_18.rational.contains p := by
  rw [← plane_0_15_18_eq]
  exact sourcePlane_sound 0 15 18 p h

end ElevenSquare.Pending.T04Completeness
