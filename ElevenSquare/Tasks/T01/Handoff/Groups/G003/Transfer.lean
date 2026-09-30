import ElevenSquare.Tasks.T01.Handoff.Groups.G003.Support
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge
import ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup
import ElevenSquare.Tasks.T01.Handoff.Inventory

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G003
open ElevenSquare.Pending
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def indices00 : List ℕ := [2, 7, 11, 14, 15, 16, 17, 29, 39, 48, 50, 51, 57, 61]
theorem finite00 : ∀ n ∈ indices00, 0 ≤ n ∧ n < 64 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk0[n-0]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk0[n-0]!))) := by
  decide
theorem support00 (k : Fin 2184) (hk : k.val ∈ indices00) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite00 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk00 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices01 : List ℕ := [65, 66, 67, 71, 75, 76, 77, 81, 82, 83, 87, 88, 89, 127]
theorem finite01 : ∀ n ∈ indices01, 64 ≤ n ∧ n < 128 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk1[n-64]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk1[n-64]!))) := by
  decide
theorem support01 (k : Fin 2184) (hk : k.val ∈ indices01) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite01 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk01 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices02 : List ℕ := [131, 134, 135, 136, 137, 141, 144, 145, 146, 147, 151, 152, 153, 155, 156, 157, 158, 159, 164, 173, 175, 176, 183, 185, 186]
theorem finite02 : ∀ n ∈ indices02, 128 ≤ n ∧ n < 192 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk2[n-128]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk2[n-128]!))) := by
  decide
theorem support02 (k : Fin 2184) (hk : k.val ∈ indices02) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite02 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk02 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices03 : List ℕ := [192, 193, 194, 196, 200, 201, 202, 206, 207, 208, 212, 213, 214, 216, 217, 218, 222, 223, 224, 226, 227, 228, 230, 253]
theorem finite03 : ∀ n ∈ indices03, 192 ≤ n ∧ n < 256 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk3[n-192]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk3[n-192]!))) := by
  decide
theorem support03 (k : Fin 2184) (hk : k.val ∈ indices03) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite03 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk03 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices04 : List ℕ := [257, 260, 261, 262, 263, 267, 270, 271, 272, 273, 277, 278, 279, 281, 282, 283, 284, 285, 290, 299, 301, 302, 309, 311, 312, 318, 319]
theorem finite04 : ∀ n ∈ indices04, 256 ≤ n ∧ n < 320 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk4[n-256]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk4[n-256]!))) := by
  decide
theorem support04 (k : Fin 2184) (hk : k.val ∈ indices04) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite04 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk04 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices05 : List ℕ := [320, 322, 326, 327, 328, 332, 333, 334, 338, 339, 340, 342, 343, 344, 348, 349, 350, 352, 353, 354, 356, 378, 381, 382, 383]
theorem finite05 : ∀ n ∈ indices05, 320 ≤ n ∧ n < 384 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk5[n-320]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk5[n-320]!))) := by
  decide
theorem support05 (k : Fin 2184) (hk : k.val ∈ indices05) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite05 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk05 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices06 : List ℕ := [384, 388, 389, 390, 392, 393, 394, 395, 396, 398, 399, 400, 402, 403, 404, 405, 406, 408, 409, 410, 411, 412, 415, 417, 418, 424, 425, 426, 429, 430, 431, 433, 434, 435, 436, 440, 441, 442, 444, 445, 446]
theorem finite06 : ∀ n ∈ indices06, 384 ≤ n ∧ n < 448 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk6[n-384]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk6[n-384]!))) := by
  decide
theorem support06 (k : Fin 2184) (hk : k.val ∈ indices06) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite06 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk06 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices07 : List ℕ := [448, 449, 450, 451, 453, 467, 477, 486, 488, 489, 497, 506, 508, 509]
theorem finite07 : ∀ n ∈ indices07, 448 ≤ n ∧ n < 512 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk7[n-448]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk7[n-448]!))) := by
  decide
theorem support07 (k : Fin 2184) (hk : k.val ∈ indices07) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite07 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk07 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices08 : List ℕ := [516, 518, 519, 525, 526, 527]
theorem finite08 : ∀ n ∈ indices08, 512 ≤ n ∧ n < 576 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk8[n-512]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk8[n-512]!))) := by
  decide
theorem support08 (k : Fin 2184) (hk : k.val ∈ indices08) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite08 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk08 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices09 : List ℕ := [587, 596, 598, 599, 606, 608, 609, 615, 616, 617, 621, 623, 624, 630, 631, 632, 635, 636, 637]
theorem finite09 : ∀ n ∈ indices09, 576 ≤ n ∧ n < 640 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk9[n-576]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk9[n-576]!))) := by
  decide
theorem support09 (k : Fin 2184) (hk : k.val ∈ indices09) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite09 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk09 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices10 : List ℕ := [665, 674, 676, 677, 684, 686, 687, 693, 694, 695, 699, 701, 702]
theorem finite10 : ∀ n ∈ indices10, 640 ≤ n ∧ n < 704 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk10[n-640]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk10[n-640]!))) := by
  decide
theorem support10 (k : Fin 2184) (hk : k.val ∈ indices10) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite10 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk10 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices11 : List ℕ := [708, 709, 710, 713, 714, 715, 740, 742, 743, 749, 750, 751, 753, 754, 755, 757, 758, 759, 765]
theorem finite11 : ∀ n ∈ indices11, 704 ≤ n ∧ n < 768 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk11[n-704]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk11[n-704]!))) := by
  decide
theorem support11 (k : Fin 2184) (hk : k.val ∈ indices11) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite11 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk11 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices12 : List ℕ := [769, 773, 774, 775, 779, 783, 784, 785, 789, 790, 791, 795, 796, 797]
theorem finite12 : ∀ n ∈ indices12, 768 ≤ n ∧ n < 832 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk12[n-768]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk12[n-768]!))) := by
  decide
theorem support12 (k : Fin 2184) (hk : k.val ∈ indices12) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite12 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk12 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices13 : List ℕ := [833, 837, 838, 839, 843, 844, 845, 849, 850, 851, 853, 854, 855, 859, 860, 861, 863, 864, 865, 885, 889, 890, 891, 895]
theorem finite13 : ∀ n ∈ indices13, 832 ≤ n ∧ n < 896 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk13[n-832]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk13[n-832]!))) := by
  decide
theorem support13 (k : Fin 2184) (hk : k.val ∈ indices13) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite13 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk13 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices14 : List ℕ := [896, 897, 901, 902, 903, 905, 906, 907, 911, 912, 913, 915, 916, 917, 937, 938, 939, 943, 944, 945, 947, 948, 949, 951, 952, 953, 957]
theorem finite14 : ∀ n ∈ indices14, 896 ≤ n ∧ n < 960 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk14[n-896]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk14[n-896]!))) := by
  decide
theorem support14 (k : Fin 2184) (hk : k.val ∈ indices14) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite14 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk14 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices15 : List ℕ := [961, 962, 963, 967, 968, 969, 973, 974, 975, 977, 978, 979, 983, 984, 985, 987, 988, 989, 1008, 1009, 1010, 1014, 1015, 1016, 1018, 1019, 1020, 1021, 1022, 1023]
theorem finite15 : ∀ n ∈ indices15, 960 ≤ n ∧ n < 1024 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk15[n-960]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk15[n-960]!))) := by
  decide
theorem support15 (k : Fin 2184) (hk : k.val ∈ indices15) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite15 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk15 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices16 : List ℕ := [1027, 1028, 1029, 1033, 1034, 1035, 1037, 1038, 1039, 1040, 1041, 1042, 1046, 1047, 1048]
theorem finite16 : ∀ n ∈ indices16, 1024 ≤ n ∧ n < 1088 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk16[n-1024]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk16[n-1024]!))) := by
  decide
theorem support16 (k : Fin 2184) (hk : k.val ∈ indices16) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite16 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk16 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices18 : List ℕ := [1162, 1166, 1169, 1170, 1171, 1172, 1176, 1179, 1180, 1181, 1182, 1186, 1187, 1188, 1190, 1191, 1192, 1193, 1194, 1198, 1207, 1209, 1210]
theorem finite18 : ∀ n ∈ indices18, 1152 ≤ n ∧ n < 1216 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk18[n-1152]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk18[n-1152]!))) := by
  decide
theorem support18 (k : Fin 2184) (hk : k.val ∈ indices18) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite18 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk18 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices19 : List ℕ := [1216, 1218, 1219, 1224, 1225, 1226, 1230, 1231, 1232, 1236, 1237, 1238, 1242, 1243, 1244, 1245, 1246, 1247, 1251, 1252, 1253, 1254, 1255, 1256, 1272, 1275, 1276, 1277, 1278]
theorem finite19 : ∀ n ∈ indices19, 1216 ≤ n ∧ n < 1280 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk19[n-1216]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk19[n-1216]!))) := by
  decide
theorem support19 (k : Fin 2184) (hk : k.val ∈ indices19) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite19 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk19 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices20 : List ℕ := [1282, 1283, 1284, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1305, 1307, 1308, 1313, 1314, 1316, 1317, 1318, 1319, 1320, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1334, 1337, 1338, 1339, 1340]
theorem finite20 : ∀ n ∈ indices20, 1280 ≤ n ∧ n < 1344 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk20[n-1280]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk20[n-1280]!))) := by
  decide
theorem support20 (k : Fin 2184) (hk : k.val ∈ indices20) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite20 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk20 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices21 : List ℕ := [1344, 1345, 1346, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1367, 1369, 1370, 1375, 1376, 1378, 1379, 1380, 1381, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1394, 1395, 1396, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406]
theorem finite21 : ∀ n ∈ indices21, 1344 ≤ n ∧ n < 1408 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk21[n-1344]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk21[n-1344]!))) := by
  decide
theorem support21 (k : Fin 2184) (hk : k.val ∈ indices21) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite21 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk21 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices22 : List ℕ := [1408, 1409, 1410, 1414, 1423, 1425, 1426, 1432, 1434, 1435, 1440, 1443, 1445, 1446, 1451, 1453, 1470]
theorem finite22 : ∀ n ∈ indices22, 1408 ≤ n ∧ n < 1472 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk22[n-1408]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk22[n-1408]!))) := by
  decide
theorem support22 (k : Fin 2184) (hk : k.val ∈ indices22) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite22 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk22 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices23 : List ℕ := [1472, 1473, 1477, 1479, 1481, 1486, 1488, 1489, 1493, 1495, 1497, 1501, 1502, 1506, 1507, 1508, 1512, 1513, 1514, 1518, 1519, 1520, 1521, 1522, 1526, 1527, 1528, 1529]
theorem finite23 : ∀ n ∈ indices23, 1472 ≤ n ∧ n < 1536 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk23[n-1472]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk23[n-1472]!))) := by
  decide
theorem support23 (k : Fin 2184) (hk : k.val ∈ indices23) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite23 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk23 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices24 : List ℕ := [1542, 1543, 1544, 1547, 1548, 1549, 1550, 1551, 1552, 1555, 1556, 1557, 1560, 1561, 1562, 1563, 1564, 1565, 1568, 1569, 1570, 1571, 1572, 1575, 1576, 1577, 1578, 1579, 1580, 1583, 1584, 1585, 1586]
theorem finite24 : ∀ n ∈ indices24, 1536 ≤ n ∧ n < 1600 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk24[n-1536]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk24[n-1536]!))) := by
  decide
theorem support24 (k : Fin 2184) (hk : k.val ∈ indices24) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite24 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk24 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices25 : List ℕ := [1607, 1611, 1614, 1615, 1616, 1617, 1620, 1623, 1624, 1625, 1626, 1629, 1630, 1631, 1633, 1634, 1635, 1639, 1647, 1649, 1654, 1656, 1660, 1661]
theorem finite25 : ∀ n ∈ indices25, 1600 ≤ n ∧ n < 1664 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk25[n-1600]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk25[n-1600]!))) := by
  decide
theorem support25 (k : Fin 2184) (hk : k.val ∈ indices25) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite25 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk25 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices26 : List ℕ := [1665, 1666, 1667, 1670, 1671, 1672, 1675, 1676, 1677, 1678, 1679, 1682, 1683, 1684, 1685, 1697, 1700, 1701, 1702, 1703, 1706, 1707, 1708, 1710, 1711, 1712, 1713, 1714, 1715, 1717, 1718, 1719, 1720, 1721, 1724, 1726]
theorem finite26 : ∀ n ∈ indices26, 1664 ≤ n ∧ n < 1728 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk26[n-1664]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk26[n-1664]!))) := by
  decide
theorem support26 (k : Fin 2184) (hk : k.val ∈ indices26) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite26 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk26 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices27 : List ℕ := [1730, 1732, 1733, 1734, 1735, 1738, 1739, 1740, 1741, 1742, 1744, 1747, 1748, 1749, 1750, 1753, 1754, 1755, 1757, 1758, 1759, 1760, 1761, 1762, 1764, 1765, 1766, 1767, 1768, 1771, 1773, 1777, 1779, 1780, 1781, 1784, 1785, 1786, 1787, 1789, 1790, 1791]
theorem finite27 : ∀ n ∈ indices27, 1728 ≤ n ∧ n < 1792 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk27[n-1728]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk27[n-1728]!))) := by
  decide
theorem support27 (k : Fin 2184) (hk : k.val ∈ indices27) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite27 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk27 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices28 : List ℕ := [1793, 1794, 1795, 1796, 1797, 1799, 1803, 1811, 1813, 1818, 1820, 1826, 1828, 1844, 1846, 1854]
theorem finite28 : ∀ n ∈ indices28, 1792 ≤ n ∧ n < 1856 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk28[n-1792]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk28[n-1792]!))) := by
  decide
theorem support28 (k : Fin 2184) (hk : k.val ∈ indices28) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite28 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk28 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices29 : List ℕ := [1856, 1863, 1867, 1868, 1869, 1872, 1873, 1874, 1877, 1878, 1879, 1880, 1883, 1884, 1893, 1894, 1895, 1897, 1898, 1899, 1901, 1902, 1903, 1905, 1906, 1907, 1909, 1910, 1911, 1912, 1914, 1915, 1916, 1918, 1919]
theorem finite29 : ∀ n ∈ indices29, 1856 ≤ n ∧ n < 1920 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk29[n-1856]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk29[n-1856]!))) := by
  decide
theorem support29 (k : Fin 2184) (hk : k.val ∈ indices29) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite29 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk29 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices30 : List ℕ := [1931, 1934, 1935, 1936, 1937, 1939, 1940, 1941, 1943, 1944, 1945, 1946, 1948, 1949, 1952, 1957, 1958, 1960, 1961, 1962, 1964, 1965, 1967, 1968, 1969, 1971, 1972, 1973, 1975, 1976, 1977, 1979, 1980]
theorem finite30 : ∀ n ∈ indices30, 1920 ≤ n ∧ n < 1984 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk30[n-1920]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk30[n-1920]!))) := by
  decide
theorem support30 (k : Fin 2184) (hk : k.val ∈ indices30) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite30 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk30 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices31 : List ℕ := [1991, 1992, 1994, 1995, 1996, 1998, 1999, 2000]
theorem finite31 : ∀ n ∈ indices31, 1984 ≤ n ∧ n < 2048 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk31[n-1984]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk31[n-1984]!))) := by
  decide
theorem support31 (k : Fin 2184) (hk : k.val ∈ indices31) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite31 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk31 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices : List ℕ := indices00 ++ indices01 ++ indices02 ++ indices03 ++ indices04 ++ indices05 ++ indices06 ++ indices07 ++ indices08 ++ indices09 ++ indices10 ++ indices11 ++ indices12 ++ indices13 ++ indices14 ++ indices15 ++ indices16 ++ indices18 ++ indices19 ++ indices20 ++ indices21 ++ indices22 ++ indices23 ++ indices24 ++ indices25 ++ indices26 ++ indices27 ++ indices28 ++ indices29 ++ indices30 ++ indices31
theorem indices_eq : indices = groupCases (3 : Group) := by decide

theorem public_support (k : Fin 2184) (hk : k.val ∈ groupCases (3 : Group)) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have hi : k.val ∈ indices := by rw [indices_eq]; exact hk
  simp only [indices, List.mem_append, or_assoc] at hi
  rcases hi with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · exact support00 k h00
  · exact support01 k h01
  · exact support02 k h02
  · exact support03 k h03
  · exact support04 k h04
  · exact support05 k h05
  · exact support06 k h06
  · exact support07 k h07
  · exact support08 k h08
  · exact support09 k h09
  · exact support10 k h10
  · exact support11 k h11
  · exact support12 k h12
  · exact support13 k h13
  · exact support14 k h14
  · exact support15 k h15
  · exact support16 k h16
  · exact support18 k h18
  · exact support19 k h19
  · exact support20 k h20
  · exact support21 k h21
  · exact support22 k h22
  · exact support23 k h23
  · exact support24 k h24
  · exact support25 k h25
  · exact support26 k h26
  · exact support27 k h27
  · exact support28 k h28
  · exact support29 k h29
  · exact support30 k h30
  · exact support31 k h31

theorem exclusion_of_capture (hcap : SupportCapture)
    (k : Fin 2184) (hk : k.val ∈ groupCases (3 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_support_or_halfTurn hcap (caseMask k) (public_support k hk) P hc ho

end ElevenSquare.Tasks.T01.Handoff.Groups.G003
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.public_support
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.exclusion_of_capture
