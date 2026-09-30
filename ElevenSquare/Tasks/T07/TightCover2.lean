import ElevenSquare.Tasks.T07.TightCoverChecks

/-! Untrusted generated dyadic tree, checked by Lean at every leaf. -/
namespace ElevenSquare
set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

theorem tightQ2_0 : TightBoxCovered 0 (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf 0 (1 / 2) (1 / 32) (206181 / 2000000) (400379 / 1000000) (206181 / 2000000) (130871 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_1 : TightBoxCovered (1 / 32) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 32) (1 / 2) (1 / 32) (206181 / 2000000) (400379 / 1000000) (143681 / 2000000) (130871 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_2 : TightBoxCovered 0 (17 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf 0 (17 / 32) (1 / 256) (206181 / 2000000) (400379 / 1000000) (206181 / 2000000) (539109 / 4000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_3 : TightBoxCovered (1 / 256) (17 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf (1 / 256) (17 / 32) (1 / 256) (206181 / 2000000) (400379 / 1000000) (396737 / 4000000) (539109 / 4000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_4 : TightBoxCovered 0 (137 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf 0 (137 / 256) (1 / 256) (54561 / 500000) (332237 / 500000) (54561 / 500000) (517271 / 4000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_5 : TightBoxCovered (1 / 256) (137 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (1 / 256) (137 / 256) (1 / 256) (54561 / 500000) (332237 / 500000) (420863 / 4000000) (517271 / 4000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_6 : TightBoxCovered 0 (17 / 32) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_2 using 1 <;> norm_num
  · convert tightQ2_3 using 1 <;> norm_num
  · convert tightQ2_4 using 1 <;> norm_num
  · convert tightQ2_5 using 1 <;> norm_num

theorem tightQ2_7 : TightBoxCovered (1 / 128) (17 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 128) (17 / 32) (1 / 128) (206181 / 2000000) (400379 / 1000000) (47639 / 500000) (277367 / 2000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_8 : TightBoxCovered 0 (69 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf 0 (69 / 128) (1 / 128) (54561 / 500000) (332237 / 500000) (54561 / 500000) (250823 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_9 : TightBoxCovered (1 / 128) (69 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 128) (69 / 128) (1 / 128) (54561 / 500000) (332237 / 500000) (202619 / 2000000) (250823 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_10 : TightBoxCovered 0 (17 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_6 using 1 <;> norm_num
  · convert tightQ2_7 using 1 <;> norm_num
  · convert tightQ2_8 using 1 <;> norm_num
  · convert tightQ2_9 using 1 <;> norm_num

theorem tightQ2_11 : TightBoxCovered (1 / 64) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 64) (17 / 32) (1 / 64) (54561 / 500000) (332237 / 500000) (93497 / 1000000) (16653 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_12 : TightBoxCovered 0 (35 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf 0 (35 / 64) (1 / 64) (54561 / 500000) (332237 / 500000) (54561 / 500000) (117599 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_13 : TightBoxCovered (1 / 64) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 64) (35 / 64) (1 / 64) (54561 / 500000) (332237 / 500000) (93497 / 1000000) (117599 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_14 : TightBoxCovered 0 (17 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_10 using 1 <;> norm_num
  · convert tightQ2_11 using 1 <;> norm_num
  · convert tightQ2_12 using 1 <;> norm_num
  · convert tightQ2_13 using 1 <;> norm_num

theorem tightQ2_15 : TightBoxCovered (1 / 32) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 32) (17 / 32) (1 / 32) (54561 / 500000) (332237 / 500000) (4867 / 62500) (16653 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_16 : TightBoxCovered 0 (1 / 2) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_0 using 1 <;> norm_num
  · convert tightQ2_1 using 1 <;> norm_num
  · convert tightQ2_14 using 1 <;> norm_num
  · convert tightQ2_15 using 1 <;> norm_num

theorem tightQ2_17 : TightBoxCovered (1 / 16) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 16) (1 / 2) (1 / 16) (206181 / 2000000) (400379 / 1000000) (81181 / 2000000) (162121 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_18 : TightBoxCovered 0 (9 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf 0 (9 / 16) (1 / 16) (54561 / 500000) (332237 / 500000) (54561 / 500000) (50987 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_19 : TightBoxCovered (1 / 16) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 16) (9 / 16) (1 / 16) (54561 / 500000) (332237 / 500000) (23311 / 500000) (50987 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_20 : TightBoxCovered 0 (1 / 2) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_16 using 1 <;> norm_num
  · convert tightQ2_17 using 1 <;> norm_num
  · convert tightQ2_18 using 1 <;> norm_num
  · convert tightQ2_19 using 1 <;> norm_num

theorem tightQ2_21 : TightBoxCovered (1 / 8) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 8) (1 / 2) (1 / 32) (206181 / 2000000) (400379 / 1000000) (106319 / 2000000) (130871 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_22 : TightBoxCovered (5 / 32) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 32) (1 / 2) (1 / 32) (206181 / 2000000) (400379 / 1000000) (168819 / 2000000) (130871 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_23 : TightBoxCovered (1 / 8) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 8) (17 / 32) (1 / 32) (54561 / 500000) (332237 / 500000) (5891 / 125000) (16653 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_24 : TightBoxCovered (5 / 32) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 32) (17 / 32) (1 / 32) (54561 / 500000) (332237 / 500000) (39189 / 500000) (16653 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_25 : TightBoxCovered (1 / 8) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_21 using 1 <;> norm_num
  · convert tightQ2_22 using 1 <;> norm_num
  · convert tightQ2_23 using 1 <;> norm_num
  · convert tightQ2_24 using 1 <;> norm_num

theorem tightQ2_26 : TightBoxCovered (3 / 16) (1 / 2) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) (1 / 2) (1 / 64) (206181 / 2000000) (400379 / 1000000) (200069 / 2000000) (57623 / 500000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_27 : TightBoxCovered (13 / 64) (1 / 2) (1 / 64) := by
  apply tightBoxCovered_leaf (13 / 64) (1 / 2) (1 / 64) (206181 / 2000000) (400379 / 1000000) (231319 / 2000000) (57623 / 500000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_28 : TightBoxCovered (3 / 16) (33 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) (33 / 64) (1 / 64) (206181 / 2000000) (400379 / 1000000) (200069 / 2000000) (130871 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_29 : TightBoxCovered (13 / 64) (33 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (33 / 64) (1 / 128) (206181 / 2000000) (400379 / 1000000) (107847 / 1000000) (246117 / 2000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_30 : TightBoxCovered (27 / 128) (33 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (33 / 64) (1 / 128) (206181 / 2000000) (400379 / 1000000) (231319 / 2000000) (246117 / 2000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_31 : TightBoxCovered (13 / 64) (67 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (67 / 128) (1 / 128) (206181 / 2000000) (400379 / 1000000) (107847 / 1000000) (130871 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_32 : TightBoxCovered (27 / 128) (67 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (67 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (307611 / 2000000) (3027 / 50000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_33 : TightBoxCovered (13 / 64) (33 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_29 using 1 <;> norm_num
  · convert tightQ2_30 using 1 <;> norm_num
  · convert tightQ2_31 using 1 <;> norm_num
  · convert tightQ2_32 using 1 <;> norm_num

theorem tightQ2_34 : TightBoxCovered (3 / 16) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_26 using 1 <;> norm_num
  · convert tightQ2_27 using 1 <;> norm_num
  · convert tightQ2_28 using 1 <;> norm_num
  · convert tightQ2_33 using 1 <;> norm_num

theorem tightQ2_35 : TightBoxCovered (7 / 32) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (1 / 2) (1 / 32) (364743 / 1000000) (233591 / 400000) (145993 / 1000000) (33591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_36 : TightBoxCovered (3 / 16) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) (17 / 32) (1 / 64) (54561 / 500000) (332237 / 500000) (94003 / 1000000) (16653 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_37 : TightBoxCovered (13 / 64) (17 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (17 / 32) (1 / 128) (54561 / 500000) (332237 / 500000) (203631 / 2000000) (16653 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_38 : TightBoxCovered (27 / 128) (17 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (17 / 32) (1 / 128) (364743 / 1000000) (233591 / 400000) (307611 / 2000000) (21091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_39 : TightBoxCovered (13 / 64) (69 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (69 / 128) (1 / 128) (54561 / 500000) (332237 / 500000) (203631 / 2000000) (250823 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_40 : TightBoxCovered (27 / 128) (69 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (69 / 128) (1 / 128) (54561 / 500000) (332237 / 500000) (27407 / 250000) (250823 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_41 : TightBoxCovered (13 / 64) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_37 using 1 <;> norm_num
  · convert tightQ2_38 using 1 <;> norm_num
  · convert tightQ2_39 using 1 <;> norm_num
  · convert tightQ2_40 using 1 <;> norm_num

theorem tightQ2_42 : TightBoxCovered (3 / 16) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) (35 / 64) (1 / 64) (54561 / 500000) (332237 / 500000) (94003 / 1000000) (117599 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_43 : TightBoxCovered (13 / 64) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (13 / 64) (35 / 64) (1 / 64) (54561 / 500000) (332237 / 500000) (27407 / 250000) (117599 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_44 : TightBoxCovered (3 / 16) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_36 using 1 <;> norm_num
  · convert tightQ2_41 using 1 <;> norm_num
  · convert tightQ2_42 using 1 <;> norm_num
  · convert tightQ2_43 using 1 <;> norm_num

theorem tightQ2_45 : TightBoxCovered (7 / 32) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (17 / 32) (1 / 32) (364743 / 1000000) (233591 / 400000) (145993 / 1000000) (21091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_46 : TightBoxCovered (3 / 16) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_34 using 1 <;> norm_num
  · convert tightQ2_35 using 1 <;> norm_num
  · convert tightQ2_44 using 1 <;> norm_num
  · convert tightQ2_45 using 1 <;> norm_num

theorem tightQ2_47 : TightBoxCovered (1 / 8) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (9 / 16) (1 / 16) (54561 / 500000) (332237 / 500000) (39189 / 500000) (50987 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_48 : TightBoxCovered (3 / 16) (9 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (9 / 16) (1 / 32) (54561 / 500000) (332237 / 500000) (27407 / 250000) (50987 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_49 : TightBoxCovered (7 / 32) (9 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (9 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (145993 / 1000000) (8591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_50 : TightBoxCovered (3 / 16) (19 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (19 / 32) (1 / 32) (54561 / 500000) (332237 / 500000) (27407 / 250000) (17681 / 250000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_51 : TightBoxCovered (7 / 32) (19 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (19 / 32) (1 / 32) (54561 / 500000) (332237 / 500000) (70439 / 500000) (17681 / 250000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_52 : TightBoxCovered (3 / 16) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_48 using 1 <;> norm_num
  · convert tightQ2_49 using 1 <;> norm_num
  · convert tightQ2_50 using 1 <;> norm_num
  · convert tightQ2_51 using 1 <;> norm_num

theorem tightQ2_53 : TightBoxCovered (1 / 8) (1 / 2) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_25 using 1 <;> norm_num
  · convert tightQ2_46 using 1 <;> norm_num
  · convert tightQ2_47 using 1 <;> norm_num
  · convert tightQ2_52 using 1 <;> norm_num

theorem tightQ2_54 : TightBoxCovered 0 (5 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf 0 (5 / 8) (1 / 8) (54561 / 500000) (332237 / 500000) (54561 / 500000) (42763 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_55 : TightBoxCovered (1 / 8) (5 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 8) (5 / 8) (1 / 8) (54561 / 500000) (332237 / 500000) (70439 / 500000) (42763 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_56 : TightBoxCovered 0 (1 / 2) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ2_20 using 1 <;> norm_num
  · convert tightQ2_53 using 1 <;> norm_num
  · convert tightQ2_54 using 1 <;> norm_num
  · convert tightQ2_55 using 1 <;> norm_num

theorem tightQ2_57 : TightBoxCovered (1 / 4) (1 / 2) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 4) (1 / 2) (1 / 8) (364743 / 1000000) (233591 / 400000) (114743 / 1000000) (33591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_58 : TightBoxCovered (3 / 8) (1 / 2) (1 / 8) := by
  apply tightBoxCovered_leaf (3 / 8) (1 / 2) (1 / 8) (364743 / 1000000) (233591 / 400000) (135257 / 1000000) (33591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_59 : TightBoxCovered (1 / 4) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 4) (5 / 8) (1 / 16) (364743 / 1000000) (233591 / 400000) (114743 / 1000000) (41409 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_60 : TightBoxCovered (5 / 16) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 16) (5 / 8) (1 / 16) (364743 / 1000000) (233591 / 400000) (52243 / 1000000) (41409 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_61 : TightBoxCovered (1 / 4) (11 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (11 / 16) (1 / 64) (54561 / 500000) (332237 / 500000) (156503 / 1000000) (38651 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_62 : TightBoxCovered (17 / 64) (11 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (11 / 16) (1 / 64) (364743 / 1000000) (233591 / 400000) (49559 / 500000) (47659 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_63 : TightBoxCovered (1 / 4) (45 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (45 / 64) (1 / 64) (54561 / 500000) (332237 / 500000) (156503 / 1000000) (13569 / 250000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_64 : TightBoxCovered (17 / 64) (45 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (45 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (49559 / 500000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_65 : TightBoxCovered (1 / 4) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_61 using 1 <;> norm_num
  · convert tightQ2_62 using 1 <;> norm_num
  · convert tightQ2_63 using 1 <;> norm_num
  · convert tightQ2_64 using 1 <;> norm_num

theorem tightQ2_66 : TightBoxCovered (9 / 32) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (11 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (83493 / 1000000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_67 : TightBoxCovered (1 / 4) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (23 / 32) (1 / 128) (54561 / 500000) (332237 / 500000) (297381 / 2000000) (124177 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_68 : TightBoxCovered (33 / 128) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (23 / 32) (1 / 128) (54561 / 500000) (332237 / 500000) (156503 / 1000000) (124177 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_69 : TightBoxCovered (1 / 4) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (93 / 128) (1 / 128) (54561 / 500000) (332237 / 500000) (297381 / 2000000) (69901 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_70 : TightBoxCovered (33 / 128) (93 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (33 / 128) (93 / 128) (1 / 256) (54561 / 500000) (332237 / 500000) (610387 / 4000000) (263979 / 4000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_71 : TightBoxCovered (67 / 256) (93 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 256) (93 / 128) (1 / 256) (54561 / 500000) (332237 / 500000) (156503 / 1000000) (263979 / 4000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_72 : TightBoxCovered (33 / 128) (187 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (33 / 128) (187 / 256) (1 / 256) (54561 / 500000) (332237 / 500000) (610387 / 4000000) (69901 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_73 : TightBoxCovered (67 / 256) (187 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 256) (187 / 256) (1 / 256) (732757 / 2000000) (215311 / 250000) (418639 / 4000000) (523101 / 4000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_74 : TightBoxCovered (33 / 128) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_70 using 1 <;> norm_num
  · convert tightQ2_71 using 1 <;> norm_num
  · convert tightQ2_72 using 1 <;> norm_num
  · convert tightQ2_73 using 1 <;> norm_num

theorem tightQ2_75 : TightBoxCovered (1 / 4) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_67 using 1 <;> norm_num
  · convert tightQ2_68 using 1 <;> norm_num
  · convert tightQ2_69 using 1 <;> norm_num
  · convert tightQ2_74 using 1 <;> norm_num

theorem tightQ2_76 : TightBoxCovered (17 / 64) (23 / 32) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 64) (23 / 32) (1 / 512) (54561 / 500000) (332237 / 500000) (1267649 / 8000000) (449833 / 8000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_77 : TightBoxCovered (137 / 512) (23 / 32) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 512) (23 / 32) (1 / 512) (54561 / 500000) (332237 / 500000) (641637 / 4000000) (449833 / 8000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_78 : TightBoxCovered (17 / 64) (369 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 64) (369 / 512) (1 / 512) (54561 / 500000) (332237 / 500000) (1267649 / 8000000) (232729 / 4000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_79 : TightBoxCovered (137 / 512) (369 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 512) (369 / 512) (1 / 512) (364743 / 1000000) (233591 / 400000) (777319 / 8000000) (110943 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_80 : TightBoxCovered (17 / 64) (23 / 32) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ2_76 using 1 <;> norm_num
  · convert tightQ2_77 using 1 <;> norm_num
  · convert tightQ2_78 using 1 <;> norm_num
  · convert tightQ2_79 using 1 <;> norm_num

theorem tightQ2_81 : TightBoxCovered (69 / 256) (23 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (23 / 32) (1 / 256) (364743 / 1000000) (233591 / 400000) (380847 / 4000000) (110943 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_82 : TightBoxCovered (17 / 64) (185 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 64) (185 / 256) (1 / 512) (54561 / 500000) (332237 / 500000) (1267649 / 8000000) (481083 / 8000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_83 : TightBoxCovered (137 / 512) (185 / 256) (1 / 2048) := by
  apply tightBoxCovered_leaf (137 / 512) (185 / 256) (1 / 2048) (54561 / 500000) (332237 / 500000) (5086221 / 32000000) (1877457 / 32000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_84 : TightBoxCovered (549 / 2048) (185 / 256) (1 / 2048) := by
  apply tightBoxCovered_leaf (549 / 2048) (185 / 256) (1 / 2048) (54561 / 500000) (332237 / 500000) (2550923 / 16000000) (1877457 / 32000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_85 : TightBoxCovered (137 / 512) (1481 / 2048) (1 / 2048) := by
  apply tightBoxCovered_leaf (137 / 512) (1481 / 2048) (1 / 2048) (54561 / 500000) (332237 / 500000) (5086221 / 32000000) (946541 / 16000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_86 : TightBoxCovered (549 / 2048) (1481 / 2048) (1 / 2048) := by
  apply tightBoxCovered_leaf (549 / 2048) (1481 / 2048) (1 / 2048) (364743 / 1000000) (233591 / 400000) (3093651 / 32000000) (446897 / 3200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_87 : TightBoxCovered (137 / 512) (185 / 256) (1 / 1024) := by
  apply tightBoxCovered_split
  · convert tightQ2_83 using 1 <;> norm_num
  · convert tightQ2_84 using 1 <;> norm_num
  · convert tightQ2_85 using 1 <;> norm_num
  · convert tightQ2_86 using 1 <;> norm_num

theorem tightQ2_88 : TightBoxCovered (275 / 1024) (185 / 256) (1 / 1024) := by
  apply tightBoxCovered_leaf (275 / 1024) (185 / 256) (1 / 1024) (364743 / 1000000) (233591 / 400000) (1539013 / 16000000) (446897 / 3200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_89 : TightBoxCovered (137 / 512) (741 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (137 / 512) (741 / 1024) (1 / 1024) (732757 / 2000000) (215311 / 250000) (790403 / 8000000) (2201779 / 16000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_90 : TightBoxCovered (275 / 1024) (741 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (275 / 1024) (741 / 1024) (1 / 1024) (732757 / 2000000) (215311 / 250000) (1565181 / 16000000) (2201779 / 16000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_91 : TightBoxCovered (137 / 512) (185 / 256) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ2_87 using 1 <;> norm_num
  · convert tightQ2_88 using 1 <;> norm_num
  · convert tightQ2_89 using 1 <;> norm_num
  · convert tightQ2_90 using 1 <;> norm_num

theorem tightQ2_92 : TightBoxCovered (17 / 64) (371 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 64) (371 / 512) (1 / 512) (732757 / 2000000) (215311 / 250000) (201507 / 2000000) (1093077 / 8000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_93 : TightBoxCovered (137 / 512) (371 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 512) (371 / 512) (1 / 512) (732757 / 2000000) (215311 / 250000) (790403 / 8000000) (1093077 / 8000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_94 : TightBoxCovered (17 / 64) (185 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ2_82 using 1 <;> norm_num
  · convert tightQ2_91 using 1 <;> norm_num
  · convert tightQ2_92 using 1 <;> norm_num
  · convert tightQ2_93 using 1 <;> norm_num

theorem tightQ2_95 : TightBoxCovered (69 / 256) (185 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (185 / 256) (1 / 256) (732757 / 2000000) (215311 / 250000) (387389 / 4000000) (554351 / 4000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_96 : TightBoxCovered (17 / 64) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_80 using 1 <;> norm_num
  · convert tightQ2_81 using 1 <;> norm_num
  · convert tightQ2_94 using 1 <;> norm_num
  · convert tightQ2_95 using 1 <;> norm_num

theorem tightQ2_97 : TightBoxCovered (35 / 128) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (23 / 32) (1 / 128) (364743 / 1000000) (233591 / 400000) (182611 / 2000000) (28517 / 200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_98 : TightBoxCovered (17 / 64) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 64) (93 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (201507 / 2000000) (269363 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_99 : TightBoxCovered (35 / 128) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (93 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (92941 / 1000000) (269363 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_100 : TightBoxCovered (17 / 64) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_96 using 1 <;> norm_num
  · convert tightQ2_97 using 1 <;> norm_num
  · convert tightQ2_98 using 1 <;> norm_num
  · convert tightQ2_99 using 1 <;> norm_num

theorem tightQ2_101 : TightBoxCovered (1 / 4) (47 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (47 / 64) (1 / 128) (54561 / 500000) (332237 / 500000) (297381 / 2000000) (155427 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_102 : TightBoxCovered (33 / 128) (47 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (47 / 64) (1 / 128) (732757 / 2000000) (215311 / 250000) (54283 / 500000) (126869 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_103 : TightBoxCovered (1 / 4) (95 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (95 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (232757 / 2000000) (238113 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_104 : TightBoxCovered (33 / 128) (95 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (95 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (54283 / 500000) (238113 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_105 : TightBoxCovered (1 / 4) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_101 using 1 <;> norm_num
  · convert tightQ2_102 using 1 <;> norm_num
  · convert tightQ2_103 using 1 <;> norm_num
  · convert tightQ2_104 using 1 <;> norm_num

theorem tightQ2_106 : TightBoxCovered (17 / 64) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (47 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (201507 / 2000000) (126869 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_107 : TightBoxCovered (1 / 4) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_75 using 1 <;> norm_num
  · convert tightQ2_100 using 1 <;> norm_num
  · convert tightQ2_105 using 1 <;> norm_num
  · convert tightQ2_106 using 1 <;> norm_num

theorem tightQ2_108 : TightBoxCovered (9 / 32) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (23 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (170257 / 2000000) (71247 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_109 : TightBoxCovered (1 / 4) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_65 using 1 <;> norm_num
  · convert tightQ2_66 using 1 <;> norm_num
  · convert tightQ2_107 using 1 <;> norm_num
  · convert tightQ2_108 using 1 <;> norm_num

theorem tightQ2_110 : TightBoxCovered (5 / 16) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 16) (11 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (52243 / 1000000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_111 : TightBoxCovered (11 / 32) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 32) (11 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (20993 / 1000000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_112 : TightBoxCovered (5 / 16) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 16) (23 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (107757 / 2000000) (71247 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_113 : TightBoxCovered (11 / 32) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 32) (23 / 32) (1 / 32) (364743 / 1000000) (233591 / 400000) (20993 / 1000000) (66409 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_114 : TightBoxCovered (5 / 16) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_110 using 1 <;> norm_num
  · convert tightQ2_111 using 1 <;> norm_num
  · convert tightQ2_112 using 1 <;> norm_num
  · convert tightQ2_113 using 1 <;> norm_num

theorem tightQ2_115 : TightBoxCovered (1 / 4) (5 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_59 using 1 <;> norm_num
  · convert tightQ2_60 using 1 <;> norm_num
  · convert tightQ2_109 using 1 <;> norm_num
  · convert tightQ2_114 using 1 <;> norm_num

theorem tightQ2_116 : TightBoxCovered (3 / 8) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (5 / 8) (1 / 16) (364743 / 1000000) (233591 / 400000) (72757 / 1000000) (41409 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_117 : TightBoxCovered (7 / 16) (5 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (5 / 8) (1 / 32) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (28909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_118 : TightBoxCovered (15 / 32) (5 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (5 / 8) (1 / 32) (364743 / 1000000) (233591 / 400000) (135257 / 1000000) (28909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_119 : TightBoxCovered (7 / 16) (21 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (21 / 32) (1 / 32) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (41409 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_120 : TightBoxCovered (15 / 32) (21 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (21 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (320189 / 2000000) (30817 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_121 : TightBoxCovered (7 / 16) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_117 using 1 <;> norm_num
  · convert tightQ2_118 using 1 <;> norm_num
  · convert tightQ2_119 using 1 <;> norm_num
  · convert tightQ2_120 using 1 <;> norm_num

theorem tightQ2_122 : TightBoxCovered (3 / 8) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 8) (11 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (41507 / 1000000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_123 : TightBoxCovered (13 / 32) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (13 / 32) (11 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (72757 / 1000000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_124 : TightBoxCovered (3 / 8) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 8) (23 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (79743 / 2000000) (71247 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_125 : TightBoxCovered (13 / 32) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (13 / 32) (23 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (142243 / 2000000) (71247 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_126 : TightBoxCovered (3 / 8) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_122 using 1 <;> norm_num
  · convert tightQ2_123 using 1 <;> norm_num
  · convert tightQ2_124 using 1 <;> norm_num
  · convert tightQ2_125 using 1 <;> norm_num

theorem tightQ2_127 : TightBoxCovered (7 / 16) (11 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (11 / 16) (1 / 64) (364743 / 1000000) (233591 / 400000) (44191 / 500000) (47659 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_128 : TightBoxCovered (29 / 64) (11 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (29 / 64) (11 / 16) (1 / 64) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (47659 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_129 : TightBoxCovered (7 / 16) (45 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (45 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (44191 / 500000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_130 : TightBoxCovered (29 / 64) (45 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (45 / 64) (1 / 128) (364743 / 1000000) (233591 / 400000) (192389 / 2000000) (1587 / 12500) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_131 : TightBoxCovered (59 / 128) (45 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (59 / 128) (45 / 64) (1 / 128) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (1587 / 12500) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_132 : TightBoxCovered (29 / 64) (91 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (91 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (192389 / 2000000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_133 : TightBoxCovered (59 / 128) (91 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (59 / 128) (91 / 128) (1 / 256) (364743 / 1000000) (233591 / 400000) (400403 / 4000000) (104693 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_134 : TightBoxCovered (119 / 256) (91 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (119 / 256) (91 / 128) (1 / 256) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (104693 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_135 : TightBoxCovered (59 / 128) (183 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (59 / 128) (183 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (400403 / 4000000) (53909 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_136 : TightBoxCovered (119 / 256) (183 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (119 / 256) (183 / 256) (1 / 256) (1257689 / 2000000) (687067 / 1000000) (656003 / 4000000) (31683 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_137 : TightBoxCovered (59 / 128) (91 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_133 using 1 <;> norm_num
  · convert tightQ2_134 using 1 <;> norm_num
  · convert tightQ2_135 using 1 <;> norm_num
  · convert tightQ2_136 using 1 <;> norm_num

theorem tightQ2_138 : TightBoxCovered (29 / 64) (45 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_130 using 1 <;> norm_num
  · convert tightQ2_131 using 1 <;> norm_num
  · convert tightQ2_132 using 1 <;> norm_num
  · convert tightQ2_137 using 1 <;> norm_num

theorem tightQ2_139 : TightBoxCovered (7 / 16) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_127 using 1 <;> norm_num
  · convert tightQ2_128 using 1 <;> norm_num
  · convert tightQ2_129 using 1 <;> norm_num
  · convert tightQ2_138 using 1 <;> norm_num

theorem tightQ2_140 : TightBoxCovered (15 / 32) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (11 / 16) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (320189 / 2000000) (31683 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_141 : TightBoxCovered (7 / 16) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (23 / 32) (1 / 64) (732757 / 2000000) (215311 / 250000) (173493 / 2000000) (71247 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_142 : TightBoxCovered (29 / 64) (23 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf (29 / 64) (23 / 32) (1 / 256) (364743 / 1000000) (233591 / 400000) (369153 / 4000000) (110943 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_143 : TightBoxCovered (117 / 256) (23 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf (117 / 256) (23 / 32) (1 / 256) (364743 / 1000000) (233591 / 400000) (192389 / 2000000) (110943 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_144 : TightBoxCovered (29 / 64) (185 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (29 / 64) (185 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (369153 / 4000000) (28517 / 200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_145 : TightBoxCovered (117 / 256) (185 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (117 / 256) (185 / 256) (1 / 256) (732757 / 2000000) (215311 / 250000) (94559 / 1000000) (554351 / 4000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_146 : TightBoxCovered (29 / 64) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_142 using 1 <;> norm_num
  · convert tightQ2_143 using 1 <;> norm_num
  · convert tightQ2_144 using 1 <;> norm_num
  · convert tightQ2_145 using 1 <;> norm_num

theorem tightQ2_147 : TightBoxCovered (59 / 128) (23 / 32) (1 / 512) := by
  apply tightBoxCovered_leaf (59 / 128) (23 / 32) (1 / 512) (364743 / 1000000) (233591 / 400000) (785181 / 8000000) (218761 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_148 : TightBoxCovered (237 / 512) (23 / 32) (1 / 512) := by
  apply tightBoxCovered_leaf (237 / 512) (23 / 32) (1 / 512) (364743 / 1000000) (233591 / 400000) (400403 / 4000000) (218761 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_149 : TightBoxCovered (59 / 128) (369 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (59 / 128) (369 / 512) (1 / 512) (364743 / 1000000) (233591 / 400000) (785181 / 8000000) (110943 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_150 : TightBoxCovered (237 / 512) (369 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (237 / 512) (369 / 512) (1 / 512) (1257689 / 2000000) (687067 / 1000000) (1327631 / 8000000) (142357 / 4000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_151 : TightBoxCovered (59 / 128) (23 / 32) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ2_147 using 1 <;> norm_num
  · convert tightQ2_148 using 1 <;> norm_num
  · convert tightQ2_149 using 1 <;> norm_num
  · convert tightQ2_150 using 1 <;> norm_num

theorem tightQ2_152 : TightBoxCovered (119 / 256) (23 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf (119 / 256) (23 / 32) (1 / 256) (1257689 / 2000000) (687067 / 1000000) (656003 / 4000000) (142357 / 4000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_153 : TightBoxCovered (59 / 128) (185 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (59 / 128) (185 / 256) (1 / 512) (732757 / 2000000) (215311 / 250000) (772097 / 8000000) (554351 / 4000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_154 : TightBoxCovered (237 / 512) (185 / 256) (1 / 1024) := by
  apply tightBoxCovered_leaf (237 / 512) (185 / 256) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (1327631 / 8000000) (585053 / 16000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_155 : TightBoxCovered (475 / 1024) (185 / 256) (1 / 1024) := by
  apply tightBoxCovered_leaf (475 / 1024) (185 / 256) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (2639637 / 16000000) (585053 / 16000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_156 : TightBoxCovered (237 / 512) (741 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (237 / 512) (741 / 1024) (1 / 1024) (732757 / 2000000) (215311 / 250000) (1559819 / 16000000) (2201779 / 16000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_157 : TightBoxCovered (475 / 1024) (741 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (475 / 1024) (741 / 1024) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (2639637 / 16000000) (300339 / 8000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_158 : TightBoxCovered (237 / 512) (185 / 256) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ2_154 using 1 <;> norm_num
  · convert tightQ2_155 using 1 <;> norm_num
  · convert tightQ2_156 using 1 <;> norm_num
  · convert tightQ2_157 using 1 <;> norm_num

theorem tightQ2_159 : TightBoxCovered (59 / 128) (371 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (59 / 128) (371 / 512) (1 / 512) (732757 / 2000000) (215311 / 250000) (772097 / 8000000) (1093077 / 8000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_160 : TightBoxCovered (237 / 512) (371 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (237 / 512) (371 / 512) (1 / 512) (732757 / 2000000) (215311 / 250000) (393861 / 4000000) (1093077 / 8000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_161 : TightBoxCovered (59 / 128) (185 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ2_153 using 1 <;> norm_num
  · convert tightQ2_158 using 1 <;> norm_num
  · convert tightQ2_159 using 1 <;> norm_num
  · convert tightQ2_160 using 1 <;> norm_num

theorem tightQ2_162 : TightBoxCovered (119 / 256) (185 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (119 / 256) (185 / 256) (1 / 256) (1257689 / 2000000) (687067 / 1000000) (656003 / 4000000) (78991 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_163 : TightBoxCovered (59 / 128) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_151 using 1 <;> norm_num
  · convert tightQ2_152 using 1 <;> norm_num
  · convert tightQ2_161 using 1 <;> norm_num
  · convert tightQ2_162 using 1 <;> norm_num

theorem tightQ2_164 : TightBoxCovered (29 / 64) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (93 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (94559 / 1000000) (269363 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_165 : TightBoxCovered (59 / 128) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (59 / 128) (93 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (269363 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_166 : TightBoxCovered (29 / 64) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_146 using 1 <;> norm_num
  · convert tightQ2_163 using 1 <;> norm_num
  · convert tightQ2_164 using 1 <;> norm_num
  · convert tightQ2_165 using 1 <;> norm_num

theorem tightQ2_167 : TightBoxCovered (7 / 16) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (47 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (173493 / 2000000) (126869 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_168 : TightBoxCovered (29 / 64) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (29 / 64) (47 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (126869 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_169 : TightBoxCovered (7 / 16) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_141 using 1 <;> norm_num
  · convert tightQ2_166 using 1 <;> norm_num
  · convert tightQ2_167 using 1 <;> norm_num
  · convert tightQ2_168 using 1 <;> norm_num

theorem tightQ2_170 : TightBoxCovered (15 / 32) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (23 / 32) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (320189 / 2000000) (11827 / 250000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_171 : TightBoxCovered (31 / 64) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (23 / 32) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (288939 / 2000000) (11827 / 250000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_172 : TightBoxCovered (15 / 32) (47 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 32) (47 / 64) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (320189 / 2000000) (110241 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_173 : TightBoxCovered (61 / 128) (47 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (47 / 64) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (76141 / 500000) (110241 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_174 : TightBoxCovered (15 / 32) (95 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 32) (95 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (13773 / 125000) (238113 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_175 : TightBoxCovered (61 / 128) (95 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (95 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (76141 / 500000) (62933 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_176 : TightBoxCovered (15 / 32) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_172 using 1 <;> norm_num
  · convert tightQ2_173 using 1 <;> norm_num
  · convert tightQ2_174 using 1 <;> norm_num
  · convert tightQ2_175 using 1 <;> norm_num

theorem tightQ2_177 : TightBoxCovered (31 / 64) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (47 / 64) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (288939 / 2000000) (62933 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_178 : TightBoxCovered (15 / 32) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_170 using 1 <;> norm_num
  · convert tightQ2_171 using 1 <;> norm_num
  · convert tightQ2_176 using 1 <;> norm_num
  · convert tightQ2_177 using 1 <;> norm_num

theorem tightQ2_179 : TightBoxCovered (7 / 16) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_139 using 1 <;> norm_num
  · convert tightQ2_140 using 1 <;> norm_num
  · convert tightQ2_169 using 1 <;> norm_num
  · convert tightQ2_178 using 1 <;> norm_num

theorem tightQ2_180 : TightBoxCovered (3 / 8) (5 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_116 using 1 <;> norm_num
  · convert tightQ2_121 using 1 <;> norm_num
  · convert tightQ2_126 using 1 <;> norm_num
  · convert tightQ2_179 using 1 <;> norm_num

theorem tightQ2_181 : TightBoxCovered (1 / 4) (1 / 2) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ2_57 using 1 <;> norm_num
  · convert tightQ2_58 using 1 <;> norm_num
  · convert tightQ2_115 using 1 <;> norm_num
  · convert tightQ2_180 using 1 <;> norm_num

theorem tightQ2_182 : TightBoxCovered 0 (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf 0 (3 / 4) (1 / 32) (54561 / 500000) (332237 / 500000) (54561 / 500000) (14597 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_183 : TightBoxCovered (1 / 32) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 32) (3 / 4) (1 / 32) (54561 / 500000) (332237 / 500000) (4867 / 62500) (14597 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_184 : TightBoxCovered 0 (25 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf 0 (25 / 32) (1 / 128) (54561 / 500000) (332237 / 500000) (54561 / 500000) (249177 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_185 : TightBoxCovered (1 / 128) (25 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 128) (25 / 32) (1 / 128) (54561 / 500000) (332237 / 500000) (202619 / 2000000) (249177 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_186 : TightBoxCovered 0 (101 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf 0 (101 / 128) (1 / 256) (54561 / 500000) (332237 / 500000) (54561 / 500000) (513979 / 4000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_187 : TightBoxCovered (1 / 256) (101 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (1 / 256) (101 / 128) (1 / 256) (54561 / 500000) (332237 / 500000) (420863 / 4000000) (513979 / 4000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_188 : TightBoxCovered 0 (203 / 256) (1 / 1024) := by
  apply tightBoxCovered_leaf 0 (203 / 256) (1 / 1024) (54561 / 500000) (332237 / 500000) (54561 / 500000) (2071541 / 16000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_189 : TightBoxCovered (1 / 1024) (203 / 256) (1 / 1024) := by
  apply tightBoxCovered_leaf (1 / 1024) (203 / 256) (1 / 1024) (54561 / 500000) (332237 / 500000) (1730327 / 16000000) (2071541 / 16000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_190 : TightBoxCovered 0 (813 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf 0 (813 / 1024) (1 / 1024) (268877 / 2000000) (224299 / 250000) (268877 / 2000000) (1652011 / 16000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_191 : TightBoxCovered (1 / 1024) (813 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (1 / 1024) (813 / 1024) (1 / 1024) (54561 / 500000) (332237 / 500000) (1730327 / 16000000) (1043583 / 8000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_192 : TightBoxCovered 0 (203 / 256) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ2_188 using 1 <;> norm_num
  · convert tightQ2_189 using 1 <;> norm_num
  · convert tightQ2_190 using 1 <;> norm_num
  · convert tightQ2_191 using 1 <;> norm_num

theorem tightQ2_193 : TightBoxCovered (1 / 512) (203 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (1 / 512) (203 / 256) (1 / 512) (54561 / 500000) (332237 / 500000) (857351 / 8000000) (1043583 / 8000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_194 : TightBoxCovered 0 (407 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf 0 (407 / 512) (1 / 512) (268877 / 2000000) (224299 / 250000) (268877 / 2000000) (818193 / 8000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_195 : TightBoxCovered (1 / 512) (407 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (1 / 512) (407 / 512) (1 / 512) (268877 / 2000000) (224299 / 250000) (1059883 / 8000000) (818193 / 8000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_196 : TightBoxCovered 0 (203 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ2_192 using 1 <;> norm_num
  · convert tightQ2_193 using 1 <;> norm_num
  · convert tightQ2_194 using 1 <;> norm_num
  · convert tightQ2_195 using 1 <;> norm_num

theorem tightQ2_197 : TightBoxCovered (1 / 256) (203 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (1 / 256) (203 / 256) (1 / 256) (54561 / 500000) (332237 / 500000) (420863 / 4000000) (132401 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_198 : TightBoxCovered 0 (101 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_186 using 1 <;> norm_num
  · convert tightQ2_187 using 1 <;> norm_num
  · convert tightQ2_196 using 1 <;> norm_num
  · convert tightQ2_197 using 1 <;> norm_num

theorem tightQ2_199 : TightBoxCovered (1 / 128) (101 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 128) (101 / 128) (1 / 128) (54561 / 500000) (332237 / 500000) (202619 / 2000000) (132401 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_200 : TightBoxCovered 0 (25 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_184 using 1 <;> norm_num
  · convert tightQ2_185 using 1 <;> norm_num
  · convert tightQ2_198 using 1 <;> norm_num
  · convert tightQ2_199 using 1 <;> norm_num

theorem tightQ2_201 : TightBoxCovered (1 / 64) (25 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 64) (25 / 32) (1 / 64) (54561 / 500000) (332237 / 500000) (93497 / 1000000) (132401 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_202 : TightBoxCovered 0 (51 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf 0 (51 / 64) (1 / 64) (268877 / 2000000) (224299 / 250000) (268877 / 2000000) (100321 / 1000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_203 : TightBoxCovered (1 / 64) (51 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 64) (51 / 64) (1 / 64) (268877 / 2000000) (224299 / 250000) (237627 / 2000000) (100321 / 1000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_204 : TightBoxCovered 0 (25 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_200 using 1 <;> norm_num
  · convert tightQ2_201 using 1 <;> norm_num
  · convert tightQ2_202 using 1 <;> norm_num
  · convert tightQ2_203 using 1 <;> norm_num

theorem tightQ2_205 : TightBoxCovered (1 / 32) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 32) (25 / 32) (1 / 32) (54561 / 500000) (332237 / 500000) (4867 / 62500) (74013 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_206 : TightBoxCovered 0 (3 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_182 using 1 <;> norm_num
  · convert tightQ2_183 using 1 <;> norm_num
  · convert tightQ2_204 using 1 <;> norm_num
  · convert tightQ2_205 using 1 <;> norm_num

theorem tightQ2_207 : TightBoxCovered (1 / 16) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 16) (3 / 4) (1 / 16) (54561 / 500000) (332237 / 500000) (23311 / 500000) (74013 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_208 : TightBoxCovered 0 (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf 0 (13 / 16) (1 / 16) (268877 / 2000000) (224299 / 250000) (268877 / 2000000) (10587 / 125000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_209 : TightBoxCovered (1 / 16) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 16) (13 / 16) (1 / 16) (268877 / 2000000) (224299 / 250000) (143877 / 2000000) (10587 / 125000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_210 : TightBoxCovered 0 (3 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_206 using 1 <;> norm_num
  · convert tightQ2_207 using 1 <;> norm_num
  · convert tightQ2_208 using 1 <;> norm_num
  · convert tightQ2_209 using 1 <;> norm_num

theorem tightQ2_211 : TightBoxCovered (1 / 8) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (3 / 4) (1 / 16) (54561 / 500000) (332237 / 500000) (39189 / 500000) (74013 / 500000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_212 : TightBoxCovered (3 / 16) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (3 / 4) (1 / 32) (54561 / 500000) (332237 / 500000) (27407 / 250000) (14597 / 125000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_213 : TightBoxCovered (7 / 32) (3 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 32) (3 / 4) (1 / 64) (54561 / 500000) (332237 / 500000) (125253 / 1000000) (101151 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_214 : TightBoxCovered (15 / 64) (3 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 64) (3 / 4) (1 / 128) (54561 / 500000) (332237 / 500000) (266131 / 2000000) (186677 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_215 : TightBoxCovered (31 / 128) (3 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (31 / 128) (3 / 4) (1 / 128) (54561 / 500000) (332237 / 500000) (70439 / 500000) (186677 / 2000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_216 : TightBoxCovered (15 / 64) (97 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 64) (97 / 128) (1 / 128) (54561 / 500000) (332237 / 500000) (266131 / 2000000) (101151 / 1000000) ⟨8, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_217 : TightBoxCovered (31 / 128) (97 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (31 / 128) (97 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (124191 / 1000000) (206863 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_218 : TightBoxCovered (15 / 64) (3 / 4) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_214 using 1 <;> norm_num
  · convert tightQ2_215 using 1 <;> norm_num
  · convert tightQ2_216 using 1 <;> norm_num
  · convert tightQ2_217 using 1 <;> norm_num

theorem tightQ2_219 : TightBoxCovered (7 / 32) (49 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 32) (49 / 64) (1 / 64) (268877 / 2000000) (224299 / 250000) (199873 / 2000000) (131571 / 1000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_220 : TightBoxCovered (15 / 64) (49 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 64) (49 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (264007 / 2000000) (95619 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_221 : TightBoxCovered (7 / 32) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_213 using 1 <;> norm_num
  · convert tightQ2_218 using 1 <;> norm_num
  · convert tightQ2_219 using 1 <;> norm_num
  · convert tightQ2_220 using 1 <;> norm_num

theorem tightQ2_222 : TightBoxCovered (3 / 16) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (25 / 32) (1 / 32) (268877 / 2000000) (224299 / 250000) (168623 / 2000000) (57973 / 500000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_223 : TightBoxCovered (7 / 32) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (25 / 32) (1 / 32) (268877 / 2000000) (224299 / 250000) (231123 / 2000000) (57973 / 500000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_224 : TightBoxCovered (3 / 16) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_212 using 1 <;> norm_num
  · convert tightQ2_221 using 1 <;> norm_num
  · convert tightQ2_222 using 1 <;> norm_num
  · convert tightQ2_223 using 1 <;> norm_num

theorem tightQ2_225 : TightBoxCovered (1 / 8) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (13 / 16) (1 / 16) (268877 / 2000000) (224299 / 250000) (106123 / 2000000) (10587 / 125000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_226 : TightBoxCovered (3 / 16) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 16) (13 / 16) (1 / 16) (268877 / 2000000) (224299 / 250000) (231123 / 2000000) (10587 / 125000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_227 : TightBoxCovered (1 / 8) (3 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_211 using 1 <;> norm_num
  · convert tightQ2_224 using 1 <;> norm_num
  · convert tightQ2_225 using 1 <;> norm_num
  · convert tightQ2_226 using 1 <;> norm_num

theorem tightQ2_228 : TightBoxCovered 0 (7 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf 0 (7 / 8) (1 / 8) (268877 / 2000000) (224299 / 250000) (268877 / 2000000) (25701 / 250000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_229 : TightBoxCovered (1 / 8) (7 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 8) (7 / 8) (1 / 8) (268877 / 2000000) (224299 / 250000) (231123 / 2000000) (25701 / 250000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_230 : TightBoxCovered 0 (3 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ2_210 using 1 <;> norm_num
  · convert tightQ2_227 using 1 <;> norm_num
  · convert tightQ2_228 using 1 <;> norm_num
  · convert tightQ2_229 using 1 <;> norm_num

theorem tightQ2_231 : TightBoxCovered (1 / 4) (3 / 4) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 4) (3 / 4) (1 / 8) (732757 / 2000000) (215311 / 250000) (232757 / 2000000) (27811 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_232 : TightBoxCovered (3 / 8) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (3 / 4) (1 / 16) (732757 / 2000000) (215311 / 250000) (142243 / 2000000) (27811 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_233 : TightBoxCovered (7 / 16) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (3 / 4) (1 / 32) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (27811 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_234 : TightBoxCovered (15 / 32) (3 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (3 / 4) (1 / 64) (732757 / 2000000) (215311 / 250000) (235993 / 2000000) (27811 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_235 : TightBoxCovered (31 / 64) (3 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (3 / 4) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (288939 / 2000000) (39279 / 500000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_236 : TightBoxCovered (15 / 32) (49 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (49 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (235993 / 2000000) (95619 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_237 : TightBoxCovered (31 / 64) (49 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (49 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (267243 / 2000000) (95619 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_238 : TightBoxCovered (15 / 32) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_234 using 1 <;> norm_num
  · convert tightQ2_235 using 1 <;> norm_num
  · convert tightQ2_236 using 1 <;> norm_num
  · convert tightQ2_237 using 1 <;> norm_num

theorem tightQ2_239 : TightBoxCovered (7 / 16) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (25 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (39997 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_240 : TightBoxCovered (15 / 32) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (25 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (267243 / 2000000) (39997 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_241 : TightBoxCovered (7 / 16) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_233 using 1 <;> norm_num
  · convert tightQ2_238 using 1 <;> norm_num
  · convert tightQ2_239 using 1 <;> norm_num
  · convert tightQ2_240 using 1 <;> norm_num

theorem tightQ2_242 : TightBoxCovered (3 / 8) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (13 / 16) (1 / 16) (732757 / 2000000) (215311 / 250000) (142243 / 2000000) (6093 / 125000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_243 : TightBoxCovered (7 / 16) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 16) (13 / 16) (1 / 16) (732757 / 2000000) (215311 / 250000) (267243 / 2000000) (6093 / 125000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_244 : TightBoxCovered (3 / 8) (3 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_232 using 1 <;> norm_num
  · convert tightQ2_241 using 1 <;> norm_num
  · convert tightQ2_242 using 1 <;> norm_num
  · convert tightQ2_243 using 1 <;> norm_num

theorem tightQ2_245 : TightBoxCovered (1 / 4) (7 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 4) (7 / 8) (1 / 16) (732757 / 2000000) (215311 / 250000) (232757 / 2000000) (2383 / 31250) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_246 : TightBoxCovered (5 / 16) (7 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 16) (7 / 8) (1 / 16) (732757 / 2000000) (215311 / 250000) (107757 / 2000000) (2383 / 31250) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_247 : TightBoxCovered (1 / 4) (15 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 4) (15 / 16) (1 / 32) (268877 / 2000000) (224299 / 250000) (293623 / 2000000) (35777 / 500000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_248 : TightBoxCovered (9 / 32) (15 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (15 / 16) (1 / 32) (732757 / 2000000) (215311 / 250000) (170257 / 2000000) (53753 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_249 : TightBoxCovered (1 / 4) (31 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (31 / 32) (1 / 64) (268877 / 2000000) (224299 / 250000) (262373 / 2000000) (87179 / 1000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_250 : TightBoxCovered (17 / 64) (31 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (31 / 32) (1 / 64) (732757 / 2000000) (215311 / 250000) (201507 / 2000000) (123131 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_251 : TightBoxCovered (1 / 4) (63 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (63 / 64) (1 / 64) (268877 / 2000000) (224299 / 250000) (262373 / 2000000) (25701 / 250000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_252 : TightBoxCovered (17 / 64) (63 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 64) (63 / 64) (1 / 128) (268877 / 2000000) (224299 / 250000) (138999 / 1000000) (189983 / 2000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_253 : TightBoxCovered (35 / 128) (63 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (63 / 64) (1 / 128) (732757 / 2000000) (215311 / 250000) (92941 / 1000000) (261887 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_254 : TightBoxCovered (17 / 64) (127 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 64) (127 / 128) (1 / 256) (268877 / 2000000) (224299 / 250000) (540371 / 4000000) (395591 / 4000000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_255 : TightBoxCovered (69 / 256) (127 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (127 / 128) (1 / 256) (732757 / 2000000) (215311 / 250000) (387389 / 4000000) (539399 / 4000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_256 : TightBoxCovered (17 / 64) (255 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 64) (255 / 256) (1 / 256) (268877 / 2000000) (224299 / 250000) (540371 / 4000000) (25701 / 250000) ⟨12, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_257 : TightBoxCovered (69 / 256) (255 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (255 / 256) (1 / 256) (732757 / 2000000) (215311 / 250000) (387389 / 4000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_258 : TightBoxCovered (17 / 64) (127 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_254 using 1 <;> norm_num
  · convert tightQ2_255 using 1 <;> norm_num
  · convert tightQ2_256 using 1 <;> norm_num
  · convert tightQ2_257 using 1 <;> norm_num

theorem tightQ2_259 : TightBoxCovered (35 / 128) (127 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (127 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (92941 / 1000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_260 : TightBoxCovered (17 / 64) (63 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_252 using 1 <;> norm_num
  · convert tightQ2_253 using 1 <;> norm_num
  · convert tightQ2_258 using 1 <;> norm_num
  · convert tightQ2_259 using 1 <;> norm_num

theorem tightQ2_261 : TightBoxCovered (1 / 4) (31 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_249 using 1 <;> norm_num
  · convert tightQ2_250 using 1 <;> norm_num
  · convert tightQ2_251 using 1 <;> norm_num
  · convert tightQ2_260 using 1 <;> norm_num

theorem tightQ2_262 : TightBoxCovered (9 / 32) (31 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (31 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (170257 / 2000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_263 : TightBoxCovered (1 / 4) (15 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_247 using 1 <;> norm_num
  · convert tightQ2_248 using 1 <;> norm_num
  · convert tightQ2_261 using 1 <;> norm_num
  · convert tightQ2_262 using 1 <;> norm_num

theorem tightQ2_264 : TightBoxCovered (5 / 16) (15 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 16) (15 / 16) (1 / 16) (732757 / 2000000) (215311 / 250000) (107757 / 2000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_265 : TightBoxCovered (1 / 4) (7 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_245 using 1 <;> norm_num
  · convert tightQ2_246 using 1 <;> norm_num
  · convert tightQ2_263 using 1 <;> norm_num
  · convert tightQ2_264 using 1 <;> norm_num

theorem tightQ2_266 : TightBoxCovered (3 / 8) (7 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (7 / 8) (1 / 16) (732757 / 2000000) (215311 / 250000) (142243 / 2000000) (2383 / 31250) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_267 : TightBoxCovered (7 / 16) (7 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 16) (7 / 8) (1 / 16) (732757 / 2000000) (215311 / 250000) (267243 / 2000000) (2383 / 31250) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_268 : TightBoxCovered (3 / 8) (15 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (15 / 16) (1 / 16) (732757 / 2000000) (215311 / 250000) (142243 / 2000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_269 : TightBoxCovered (7 / 16) (15 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (15 / 16) (1 / 32) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (53753 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_270 : TightBoxCovered (15 / 32) (15 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (15 / 16) (1 / 32) (313399 / 500000) (954497 / 1000000) (4939 / 31250) (16997 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_271 : TightBoxCovered (7 / 16) (31 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (31 / 32) (1 / 64) (732757 / 2000000) (215311 / 250000) (173493 / 2000000) (123131 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_272 : TightBoxCovered (29 / 64) (31 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (29 / 64) (31 / 32) (1 / 64) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (123131 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_273 : TightBoxCovered (7 / 16) (63 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (63 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (173493 / 2000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_274 : TightBoxCovered (29 / 64) (63 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (63 / 64) (1 / 128) (732757 / 2000000) (215311 / 250000) (94559 / 1000000) (261887 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_275 : TightBoxCovered (59 / 128) (63 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (59 / 128) (63 / 64) (1 / 128) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (261887 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_276 : TightBoxCovered (29 / 64) (127 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (127 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (94559 / 1000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_277 : TightBoxCovered (59 / 128) (127 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (59 / 128) (127 / 128) (1 / 256) (732757 / 2000000) (215311 / 250000) (393861 / 4000000) (539399 / 4000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_278 : TightBoxCovered (119 / 256) (127 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (119 / 256) (127 / 128) (1 / 256) (732757 / 2000000) (215311 / 250000) (204743 / 2000000) (539399 / 4000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_279 : TightBoxCovered (59 / 128) (255 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (59 / 128) (255 / 256) (1 / 512) (732757 / 2000000) (215311 / 250000) (772097 / 8000000) (1094423 / 8000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_280 : TightBoxCovered (237 / 512) (255 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (237 / 512) (255 / 256) (1 / 512) (732757 / 2000000) (215311 / 250000) (393861 / 4000000) (1094423 / 8000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_281 : TightBoxCovered (59 / 128) (511 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (59 / 128) (511 / 512) (1 / 512) (732757 / 2000000) (215311 / 250000) (772097 / 8000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_282 : TightBoxCovered (237 / 512) (511 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (237 / 512) (511 / 512) (1 / 1024) (732757 / 2000000) (215311 / 250000) (1559819 / 16000000) (2204471 / 16000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_283 : TightBoxCovered (475 / 1024) (511 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (475 / 1024) (511 / 512) (1 / 1024) (732757 / 2000000) (215311 / 250000) (393861 / 4000000) (2204471 / 16000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_284 : TightBoxCovered (237 / 512) (1023 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (237 / 512) (1023 / 1024) (1 / 1024) (732757 / 2000000) (215311 / 250000) (1559819 / 16000000) (34689 / 250000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_285 : TightBoxCovered (475 / 1024) (1023 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (475 / 1024) (1023 / 1024) (1 / 1024) (313399 / 500000) (954497 / 1000000) (2606893 / 16000000) (45503 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_286 : TightBoxCovered (237 / 512) (511 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ2_282 using 1 <;> norm_num
  · convert tightQ2_283 using 1 <;> norm_num
  · convert tightQ2_284 using 1 <;> norm_num
  · convert tightQ2_285 using 1 <;> norm_num

theorem tightQ2_287 : TightBoxCovered (59 / 128) (255 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ2_279 using 1 <;> norm_num
  · convert tightQ2_280 using 1 <;> norm_num
  · convert tightQ2_281 using 1 <;> norm_num
  · convert tightQ2_286 using 1 <;> norm_num

theorem tightQ2_288 : TightBoxCovered (119 / 256) (255 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (119 / 256) (255 / 256) (1 / 256) (313399 / 500000) (954497 / 1000000) (647817 / 4000000) (45503 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_289 : TightBoxCovered (59 / 128) (127 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ2_277 using 1 <;> norm_num
  · convert tightQ2_278 using 1 <;> norm_num
  · convert tightQ2_287 using 1 <;> norm_num
  · convert tightQ2_288 using 1 <;> norm_num

theorem tightQ2_290 : TightBoxCovered (29 / 64) (63 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ2_274 using 1 <;> norm_num
  · convert tightQ2_275 using 1 <;> norm_num
  · convert tightQ2_276 using 1 <;> norm_num
  · convert tightQ2_289 using 1 <;> norm_num

theorem tightQ2_291 : TightBoxCovered (7 / 16) (31 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ2_271 using 1 <;> norm_num
  · convert tightQ2_272 using 1 <;> norm_num
  · convert tightQ2_273 using 1 <;> norm_num
  · convert tightQ2_290 using 1 <;> norm_num

theorem tightQ2_292 : TightBoxCovered (15 / 32) (31 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (31 / 32) (1 / 32) (313399 / 500000) (954497 / 1000000) (4939 / 31250) (45503 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ2_293 : TightBoxCovered (7 / 16) (15 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ2_269 using 1 <;> norm_num
  · convert tightQ2_270 using 1 <;> norm_num
  · convert tightQ2_291 using 1 <;> norm_num
  · convert tightQ2_292 using 1 <;> norm_num

theorem tightQ2_294 : TightBoxCovered (3 / 8) (7 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ2_266 using 1 <;> norm_num
  · convert tightQ2_267 using 1 <;> norm_num
  · convert tightQ2_268 using 1 <;> norm_num
  · convert tightQ2_293 using 1 <;> norm_num

theorem tightQ2_295 : TightBoxCovered (1 / 4) (3 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ2_231 using 1 <;> norm_num
  · convert tightQ2_244 using 1 <;> norm_num
  · convert tightQ2_265 using 1 <;> norm_num
  · convert tightQ2_294 using 1 <;> norm_num

theorem tightQ2_296 : TightBoxCovered 0 (1 / 2) (1 / 2) := by
  apply tightBoxCovered_split
  · convert tightQ2_56 using 1 <;> norm_num
  · convert tightQ2_181 using 1 <;> norm_num
  · convert tightQ2_230 using 1 <;> norm_num
  · convert tightQ2_295 using 1 <;> norm_num

theorem tightQuadrant2 : TightBoxCovered 0 (1 / 2) (1/2) := tightQ2_296

end ElevenSquare
