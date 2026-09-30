import ElevenSquare.Interop.Wand125.Certificates
import ElevenSquare.Tasks.T01.Handoff.Inventory

/-! Concrete new baseline cases. Generated from the finite source comparison;
Lean checks the applicability of every listed case and disjointness from the
three previously completed groups. The Python comparison is not a proof oracle. -/

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def newCases : List ℕ := [126, 128, 129, 130, 132, 133, 138, 139, 140, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 174, 177, 178, 179, 180, 197, 199, 203, 204, 205, 209, 210, 211, 215, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 640, 739, 760, 762, 766, 770, 776, 777, 834, 840, 841, 846, 847, 852, 886, 892, 893, 898, 899, 904, 941, 946, 950, 980, 994, 1005, 1072, 1085, 1095, 1099, 1117, 1134, 1136, 1138, 1140, 1149, 1152, 1155, 1157, 1158, 1160, 1161, 1163, 1164, 1165, 1167, 1168, 1173, 1174, 1175, 1177, 1178, 1183, 1184, 1185, 1189, 1195, 1196, 1197, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1208, 1211, 1212, 1213, 1214, 1215, 1220, 1221, 1222, 1223, 1455, 1469, 1482, 1485, 1498, 1500, 1588, 1600, 1602, 1604, 1655, 1763, 1772, 1778, 1819, 1827, 1832, 1834, 1843, 1851, 1853, 1855, 1859, 1860, 1861, 1862, 1881, 1888, 1892, 1913, 1917, 1921, 1923, 1926, 1927, 1928, 1929, 1930, 1982, 1988, 1989, 1990, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2035, 2036, 2038, 2040, 2042, 2043, 2045, 2046, 2059, 2061, 2063, 2064, 2066, 2067, 2079, 2082, 2083, 2096, 2101, 2105, 2109, 2124, 2128, 2131, 2134, 2137, 2138, 2140, 2142, 2144, 2145, 2147, 2154, 2156, 2159, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172]

def checkedCase (k : ℕ) : Bool :=
  if h : k < 2184 then applicable ⟨k, h⟩ else false

theorem newCases_length : newCases.length = 247 := by decide

theorem newCases_nodup : newCases.Nodup := by decide +kernel

theorem newCases_checked : newCases.all checkedCase = true := by decide +kernel

theorem newCases_baseline : ∀ k ∈ newCases, k ∈ baselineIndices := by decide +kernel

theorem newCases_disjoint : ∀ k ∈ newCases,
    k ∉ groupCases (3 : Group) ∧ k ∉ groupCases (4 : Group) ∧
    k ∉ groupCases (7 : Group) := by decide +kernel

theorem new_case_excluded (k : Fin 2184) (hk : k.val ∈ newCases)
    (P : Packing 11 coverCap) : ¬ Occupies P (caseMask k) := by
  have h := List.all_eq_true.mp newCases_checked k.val hk
  have ha : applicable k = true := by simpa [checkedCase, k.isLt] using h
  exact excluded k ha P

end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.new_case_excluded
#print axioms ElevenSquare.Interop.Wand125.newCases_disjoint

#print axioms ElevenSquare.Interop.Wand125.newCases_baseline
