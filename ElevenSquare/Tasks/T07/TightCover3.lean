import ElevenSquare.Tasks.T07.TightCoverChecks

/-! Untrusted generated dyadic tree, checked by Lean at every leaf. -/
namespace ElevenSquare
set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

theorem tightQ3_0 : TightBoxCovered (1 / 2) (1 / 2) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (1 / 2) (1 / 64) (635257 / 1000000) (166409 / 400000) (135257 / 1000000) (39841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_1 : TightBoxCovered (33 / 64) (1 / 2) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (1 / 2) (1 / 64) (635257 / 1000000) (166409 / 400000) (7477 / 62500) (39841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_2 : TightBoxCovered (1 / 2) (33 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (33 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (75441 / 500000) (27341 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_3 : TightBoxCovered (33 / 64) (33 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (33 / 64) (1 / 64) (635257 / 1000000) (166409 / 400000) (7477 / 62500) (46091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_4 : TightBoxCovered (1 / 2) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_0 using 1 <;> norm_num
  · convert tightQ3_1 using 1 <;> norm_num
  · convert tightQ3_2 using 1 <;> norm_num
  · convert tightQ3_3 using 1 <;> norm_num

theorem tightQ3_5 : TightBoxCovered (17 / 32) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (1 / 2) (1 / 32) (635257 / 1000000) (166409 / 400000) (104007 / 1000000) (46091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_6 : TightBoxCovered (1 / 2) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (17 / 32) (1 / 64) (364743 / 1000000) (233591 / 400000) (75441 / 500000) (21091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_7 : TightBoxCovered (33 / 64) (17 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (17 / 32) (1 / 128) (364743 / 1000000) (233591 / 400000) (317389 / 2000000) (21091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_8 : TightBoxCovered (67 / 128) (17 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (67 / 128) (17 / 32) (1 / 128) (635257 / 1000000) (166409 / 400000) (223639 / 2000000) (769 / 6250) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_9 : TightBoxCovered (33 / 64) (69 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (69 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (317389 / 2000000) (8983 / 200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_10 : TightBoxCovered (67 / 128) (69 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 128) (69 / 128) (1 / 256) (635257 / 1000000) (166409 / 400000) (223639 / 2000000) (101557 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_11 : TightBoxCovered (135 / 256) (69 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (135 / 256) (69 / 128) (1 / 256) (635257 / 1000000) (166409 / 400000) (431653 / 4000000) (101557 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_12 : TightBoxCovered (67 / 128) (139 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 128) (139 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (650403 / 4000000) (32807 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_13 : TightBoxCovered (135 / 256) (139 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (135 / 256) (139 / 256) (1 / 256) (635257 / 1000000) (166409 / 400000) (431653 / 4000000) (52341 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_14 : TightBoxCovered (67 / 128) (69 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ3_10 using 1 <;> norm_num
  · convert tightQ3_11 using 1 <;> norm_num
  · convert tightQ3_12 using 1 <;> norm_num
  · convert tightQ3_13 using 1 <;> norm_num

theorem tightQ3_15 : TightBoxCovered (33 / 64) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_7 using 1 <;> norm_num
  · convert tightQ3_8 using 1 <;> norm_num
  · convert tightQ3_9 using 1 <;> norm_num
  · convert tightQ3_14 using 1 <;> norm_num

theorem tightQ3_16 : TightBoxCovered (1 / 2) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (35 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (75441 / 500000) (14841 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_17 : TightBoxCovered (33 / 64) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (35 / 64) (1 / 128) (364743 / 1000000) (233591 / 400000) (317389 / 2000000) (14841 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_18 : TightBoxCovered (67 / 128) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 128) (35 / 64) (1 / 256) (364743 / 1000000) (233591 / 400000) (650403 / 4000000) (14841 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_19 : TightBoxCovered (135 / 256) (35 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (135 / 256) (35 / 64) (1 / 512) (364743 / 1000000) (233591 / 400000) (1316431 / 8000000) (14841 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_20 : TightBoxCovered (271 / 512) (35 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (271 / 512) (35 / 64) (1 / 512) (635257 / 1000000) (166409 / 400000) (847681 / 8000000) (212489 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_21 : TightBoxCovered (135 / 256) (281 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (135 / 256) (281 / 512) (1 / 512) (364743 / 1000000) (233591 / 400000) (1316431 / 8000000) (56239 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_22 : TightBoxCovered (271 / 512) (281 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (271 / 512) (281 / 512) (1 / 1024) (364743 / 1000000) (233591 / 400000) (2648487 / 16000000) (56239 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_23 : TightBoxCovered (543 / 1024) (281 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (543 / 1024) (281 / 512) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (1577137 / 16000000) (1105911 / 8000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_24 : TightBoxCovered (271 / 512) (563 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (271 / 512) (563 / 1024) (1 / 1024) (364743 / 1000000) (233591 / 400000) (2648487 / 16000000) (109353 / 3200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_25 : TightBoxCovered (543 / 1024) (563 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (543 / 1024) (563 / 1024) (1 / 1024) (364743 / 1000000) (233591 / 400000) (166507 / 1000000) (109353 / 3200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_26 : TightBoxCovered (271 / 512) (281 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ3_22 using 1 <;> norm_num
  · convert tightQ3_23 using 1 <;> norm_num
  · convert tightQ3_24 using 1 <;> norm_num
  · convert tightQ3_25 using 1 <;> norm_num

theorem tightQ3_27 : TightBoxCovered (135 / 256) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ3_19 using 1 <;> norm_num
  · convert tightQ3_20 using 1 <;> norm_num
  · convert tightQ3_21 using 1 <;> norm_num
  · convert tightQ3_26 using 1 <;> norm_num

theorem tightQ3_28 : TightBoxCovered (67 / 128) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 128) (141 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (650403 / 4000000) (26557 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_29 : TightBoxCovered (135 / 256) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (135 / 256) (141 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (166507 / 1000000) (26557 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_30 : TightBoxCovered (67 / 128) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ3_18 using 1 <;> norm_num
  · convert tightQ3_27 using 1 <;> norm_num
  · convert tightQ3_28 using 1 <;> norm_num
  · convert tightQ3_29 using 1 <;> norm_num

theorem tightQ3_31 : TightBoxCovered (33 / 64) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (71 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (317389 / 2000000) (2929 / 100000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_32 : TightBoxCovered (67 / 128) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (67 / 128) (71 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (166507 / 1000000) (2929 / 100000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_33 : TightBoxCovered (33 / 64) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_17 using 1 <;> norm_num
  · convert tightQ3_30 using 1 <;> norm_num
  · convert tightQ3_31 using 1 <;> norm_num
  · convert tightQ3_32 using 1 <;> norm_num

theorem tightQ3_34 : TightBoxCovered (1 / 2) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_6 using 1 <;> norm_num
  · convert tightQ3_15 using 1 <;> norm_num
  · convert tightQ3_16 using 1 <;> norm_num
  · convert tightQ3_33 using 1 <;> norm_num

theorem tightQ3_35 : TightBoxCovered (17 / 32) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 32) (17 / 32) (1 / 64) (635257 / 1000000) (166409 / 400000) (104007 / 1000000) (52341 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_36 : TightBoxCovered (35 / 64) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (17 / 32) (1 / 64) (635257 / 1000000) (166409 / 400000) (44191 / 500000) (52341 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_37 : TightBoxCovered (17 / 32) (35 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 32) (35 / 64) (1 / 512) (635257 / 1000000) (166409 / 400000) (104007 / 1000000) (212489 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_38 : TightBoxCovered (273 / 512) (35 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (273 / 512) (35 / 64) (1 / 512) (635257 / 1000000) (166409 / 400000) (816431 / 8000000) (212489 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_39 : TightBoxCovered (17 / 32) (281 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 32) (281 / 512) (1 / 512) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (1105911 / 8000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_40 : TightBoxCovered (273 / 512) (281 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (273 / 512) (281 / 512) (1 / 512) (635257 / 1000000) (166409 / 400000) (816431 / 8000000) (107807 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_41 : TightBoxCovered (17 / 32) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ3_37 using 1 <;> norm_num
  · convert tightQ3_38 using 1 <;> norm_num
  · convert tightQ3_39 using 1 <;> norm_num
  · convert tightQ3_40 using 1 <;> norm_num

theorem tightQ3_42 : TightBoxCovered (137 / 256) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (137 / 256) (35 / 64) (1 / 256) (635257 / 1000000) (166409 / 400000) (400403 / 4000000) (107807 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_43 : TightBoxCovered (17 / 32) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 32) (141 / 256) (1 / 256) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (545143 / 4000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_44 : TightBoxCovered (137 / 256) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (137 / 256) (141 / 256) (1 / 256) (1257689 / 2000000) (687067 / 1000000) (374753 / 4000000) (545143 / 4000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_45 : TightBoxCovered (17 / 32) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ3_41 using 1 <;> norm_num
  · convert tightQ3_42 using 1 <;> norm_num
  · convert tightQ3_43 using 1 <;> norm_num
  · convert tightQ3_44 using 1 <;> norm_num

theorem tightQ3_46 : TightBoxCovered (69 / 128) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (35 / 64) (1 / 128) (635257 / 1000000) (166409 / 400000) (192389 / 2000000) (27733 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_47 : TightBoxCovered (17 / 32) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 32) (71 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (264759 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_48 : TightBoxCovered (69 / 128) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (71 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (44891 / 500000) (264759 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_49 : TightBoxCovered (17 / 32) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_45 using 1 <;> norm_num
  · convert tightQ3_46 using 1 <;> norm_num
  · convert tightQ3_47 using 1 <;> norm_num
  · convert tightQ3_48 using 1 <;> norm_num

theorem tightQ3_50 : TightBoxCovered (35 / 64) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (35 / 64) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (163939 / 2000000) (4381 / 31250) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_51 : TightBoxCovered (17 / 32) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_35 using 1 <;> norm_num
  · convert tightQ3_36 using 1 <;> norm_num
  · convert tightQ3_49 using 1 <;> norm_num
  · convert tightQ3_50 using 1 <;> norm_num

theorem tightQ3_52 : TightBoxCovered (1 / 2) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_4 using 1 <;> norm_num
  · convert tightQ3_5 using 1 <;> norm_num
  · convert tightQ3_34 using 1 <;> norm_num
  · convert tightQ3_51 using 1 <;> norm_num

theorem tightQ3_53 : TightBoxCovered (9 / 16) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (1 / 2) (1 / 16) (635257 / 1000000) (166409 / 400000) (72757 / 1000000) (58591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_54 : TightBoxCovered (1 / 2) (9 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (9 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (166507 / 1000000) (8591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_55 : TightBoxCovered (17 / 32) (9 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (9 / 16) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (124567 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_56 : TightBoxCovered (1 / 2) (19 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (19 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (257689 / 2000000) (93317 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_57 : TightBoxCovered (17 / 32) (19 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (19 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (93317 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_58 : TightBoxCovered (1 / 2) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_54 using 1 <;> norm_num
  · convert tightQ3_55 using 1 <;> norm_num
  · convert tightQ3_56 using 1 <;> norm_num
  · convert tightQ3_57 using 1 <;> norm_num

theorem tightQ3_59 : TightBoxCovered (9 / 16) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (9 / 16) (1 / 16) (1257689 / 2000000) (687067 / 1000000) (132689 / 2000000) (124567 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_60 : TightBoxCovered (1 / 2) (1 / 2) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_52 using 1 <;> norm_num
  · convert tightQ3_53 using 1 <;> norm_num
  · convert tightQ3_58 using 1 <;> norm_num
  · convert tightQ3_59 using 1 <;> norm_num

theorem tightQ3_61 : TightBoxCovered (5 / 8) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 8) (1 / 2) (1 / 16) (635257 / 1000000) (166409 / 400000) (52243 / 1000000) (58591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_62 : TightBoxCovered (11 / 16) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (1 / 2) (1 / 32) (635257 / 1000000) (166409 / 400000) (83493 / 1000000) (46091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_63 : TightBoxCovered (23 / 32) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (23 / 32) (1 / 2) (1 / 32) (635257 / 1000000) (166409 / 400000) (114743 / 1000000) (46091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_64 : TightBoxCovered (11 / 16) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (17 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (83493 / 1000000) (58591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_65 : TightBoxCovered (23 / 32) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (17 / 32) (1 / 64) (635257 / 1000000) (166409 / 400000) (49559 / 500000) (52341 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_66 : TightBoxCovered (47 / 64) (17 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (17 / 32) (1 / 128) (635257 / 1000000) (166409 / 400000) (213861 / 2000000) (769 / 6250) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_67 : TightBoxCovered (95 / 128) (17 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (17 / 32) (1 / 128) (635257 / 1000000) (166409 / 400000) (114743 / 1000000) (769 / 6250) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_68 : TightBoxCovered (47 / 64) (69 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (69 / 128) (1 / 128) (635257 / 1000000) (166409 / 400000) (213861 / 2000000) (52341 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_69 : TightBoxCovered (95 / 128) (69 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (69 / 128) (1 / 128) (1793819 / 2000000) (599621 / 1000000) (77361 / 500000) (121117 / 2000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_70 : TightBoxCovered (47 / 64) (17 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_66 using 1 <;> norm_num
  · convert tightQ3_67 using 1 <;> norm_num
  · convert tightQ3_68 using 1 <;> norm_num
  · convert tightQ3_69 using 1 <;> norm_num

theorem tightQ3_71 : TightBoxCovered (23 / 32) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) (35 / 64) (1 / 128) (635257 / 1000000) (166409 / 400000) (182611 / 2000000) (27733 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_72 : TightBoxCovered (93 / 128) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) (35 / 64) (1 / 256) (635257 / 1000000) (166409 / 400000) (380847 / 4000000) (107807 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_73 : TightBoxCovered (187 / 256) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (187 / 256) (35 / 64) (1 / 256) (635257 / 1000000) (166409 / 400000) (49559 / 500000) (107807 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_74 : TightBoxCovered (93 / 128) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) (141 / 256) (1 / 256) (635257 / 1000000) (166409 / 400000) (380847 / 4000000) (27733 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_75 : TightBoxCovered (187 / 256) (141 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (187 / 256) (141 / 256) (1 / 512) (635257 / 1000000) (166409 / 400000) (777319 / 8000000) (218739 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_76 : TightBoxCovered (375 / 512) (141 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (375 / 512) (141 / 256) (1 / 512) (635257 / 1000000) (166409 / 400000) (49559 / 500000) (218739 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_77 : TightBoxCovered (187 / 256) (283 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (187 / 256) (283 / 512) (1 / 512) (635257 / 1000000) (166409 / 400000) (777319 / 8000000) (27733 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_78 : TightBoxCovered (375 / 512) (283 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (375 / 512) (283 / 512) (1 / 1024) (635257 / 1000000) (166409 / 400000) (1570263 / 16000000) (440603 / 3200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_79 : TightBoxCovered (751 / 1024) (283 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (751 / 1024) (283 / 512) (1 / 1024) (635257 / 1000000) (166409 / 400000) (49559 / 500000) (440603 / 3200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_80 : TightBoxCovered (375 / 512) (567 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (375 / 512) (567 / 1024) (1 / 1024) (635257 / 1000000) (166409 / 400000) (1570263 / 16000000) (27733 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_81 : TightBoxCovered (751 / 1024) (567 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (751 / 1024) (567 / 1024) (1 / 1024) (1793819 / 2000000) (599621 / 1000000) (2616177 / 16000000) (734561 / 16000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_82 : TightBoxCovered (375 / 512) (283 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ3_78 using 1 <;> norm_num
  · convert tightQ3_79 using 1 <;> norm_num
  · convert tightQ3_80 using 1 <;> norm_num
  · convert tightQ3_81 using 1 <;> norm_num

theorem tightQ3_83 : TightBoxCovered (187 / 256) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ3_75 using 1 <;> norm_num
  · convert tightQ3_76 using 1 <;> norm_num
  · convert tightQ3_77 using 1 <;> norm_num
  · convert tightQ3_82 using 1 <;> norm_num

theorem tightQ3_84 : TightBoxCovered (93 / 128) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ3_72 using 1 <;> norm_num
  · convert tightQ3_73 using 1 <;> norm_num
  · convert tightQ3_74 using 1 <;> norm_num
  · convert tightQ3_83 using 1 <;> norm_num

theorem tightQ3_85 : TightBoxCovered (23 / 32) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) (71 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (48859 / 500000) (264759 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_86 : TightBoxCovered (93 / 128) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (93 / 128) (71 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (211061 / 2000000) (264759 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_87 : TightBoxCovered (23 / 32) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_71 using 1 <;> norm_num
  · convert tightQ3_84 using 1 <;> norm_num
  · convert tightQ3_85 using 1 <;> norm_num
  · convert tightQ3_86 using 1 <;> norm_num

theorem tightQ3_88 : TightBoxCovered (47 / 64) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (47 / 64) (35 / 64) (1 / 256) (635257 / 1000000) (166409 / 400000) (412097 / 4000000) (107807 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_89 : TightBoxCovered (189 / 256) (35 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (189 / 256) (35 / 64) (1 / 256) (1793819 / 2000000) (599621 / 1000000) (634513 / 4000000) (26373 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_90 : TightBoxCovered (47 / 64) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (47 / 64) (141 / 256) (1 / 256) (1793819 / 2000000) (599621 / 1000000) (325069 / 2000000) (195359 / 4000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_91 : TightBoxCovered (189 / 256) (141 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (189 / 256) (141 / 256) (1 / 256) (1793819 / 2000000) (599621 / 1000000) (634513 / 4000000) (195359 / 4000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_92 : TightBoxCovered (47 / 64) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ3_88 using 1 <;> norm_num
  · convert tightQ3_89 using 1 <;> norm_num
  · convert tightQ3_90 using 1 <;> norm_num
  · convert tightQ3_91 using 1 <;> norm_num

theorem tightQ3_93 : TightBoxCovered (95 / 128) (35 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (35 / 64) (1 / 128) (1793819 / 2000000) (599621 / 1000000) (77361 / 500000) (26373 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_94 : TightBoxCovered (47 / 64) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (71 / 128) (1 / 128) (1793819 / 2000000) (599621 / 1000000) (325069 / 2000000) (89867 / 2000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_95 : TightBoxCovered (95 / 128) (71 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (71 / 128) (1 / 128) (1793819 / 2000000) (599621 / 1000000) (77361 / 500000) (89867 / 2000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_96 : TightBoxCovered (47 / 64) (35 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_92 using 1 <;> norm_num
  · convert tightQ3_93 using 1 <;> norm_num
  · convert tightQ3_94 using 1 <;> norm_num
  · convert tightQ3_95 using 1 <;> norm_num

theorem tightQ3_97 : TightBoxCovered (23 / 32) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_65 using 1 <;> norm_num
  · convert tightQ3_70 using 1 <;> norm_num
  · convert tightQ3_87 using 1 <;> norm_num
  · convert tightQ3_96 using 1 <;> norm_num

theorem tightQ3_98 : TightBoxCovered (11 / 16) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_62 using 1 <;> norm_num
  · convert tightQ3_63 using 1 <;> norm_num
  · convert tightQ3_64 using 1 <;> norm_num
  · convert tightQ3_97 using 1 <;> norm_num

theorem tightQ3_99 : TightBoxCovered (5 / 8) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 8) (9 / 16) (1 / 16) (1257689 / 2000000) (687067 / 1000000) (117311 / 2000000) (124567 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_100 : TightBoxCovered (11 / 16) (9 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (9 / 16) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (179811 / 2000000) (124567 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_101 : TightBoxCovered (23 / 32) (9 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (9 / 16) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (211061 / 2000000) (124567 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_102 : TightBoxCovered (47 / 64) (9 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (9 / 16) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (325069 / 2000000) (37121 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_103 : TightBoxCovered (23 / 32) (37 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (37 / 64) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (211061 / 2000000) (54471 / 500000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_104 : TightBoxCovered (47 / 64) (37 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (37 / 64) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (242311 / 2000000) (54471 / 500000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_105 : TightBoxCovered (23 / 32) (9 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_101 using 1 <;> norm_num
  · convert tightQ3_102 using 1 <;> norm_num
  · convert tightQ3_103 using 1 <;> norm_num
  · convert tightQ3_104 using 1 <;> norm_num

theorem tightQ3_106 : TightBoxCovered (11 / 16) (19 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (19 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (179811 / 2000000) (93317 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_107 : TightBoxCovered (23 / 32) (19 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (23 / 32) (19 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (242311 / 2000000) (93317 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_108 : TightBoxCovered (11 / 16) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_100 using 1 <;> norm_num
  · convert tightQ3_105 using 1 <;> norm_num
  · convert tightQ3_106 using 1 <;> norm_num
  · convert tightQ3_107 using 1 <;> norm_num

theorem tightQ3_109 : TightBoxCovered (5 / 8) (1 / 2) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_61 using 1 <;> norm_num
  · convert tightQ3_98 using 1 <;> norm_num
  · convert tightQ3_99 using 1 <;> norm_num
  · convert tightQ3_108 using 1 <;> norm_num

theorem tightQ3_110 : TightBoxCovered (1 / 2) (5 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 2) (5 / 8) (1 / 8) (1257689 / 2000000) (687067 / 1000000) (257689 / 2000000) (62933 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_111 : TightBoxCovered (5 / 8) (5 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (5 / 8) (5 / 8) (1 / 8) (1257689 / 2000000) (687067 / 1000000) (242311 / 2000000) (62933 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_112 : TightBoxCovered (1 / 2) (1 / 2) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ3_60 using 1 <;> norm_num
  · convert tightQ3_109 using 1 <;> norm_num
  · convert tightQ3_110 using 1 <;> norm_num
  · convert tightQ3_111 using 1 <;> norm_num

theorem tightQ3_113 : TightBoxCovered (3 / 4) (1 / 2) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 4) (1 / 2) (1 / 64) (635257 / 1000000) (166409 / 400000) (2037 / 15625) (39841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_114 : TightBoxCovered (49 / 64) (1 / 2) (1 / 64) := by
  apply tightBoxCovered_leaf (49 / 64) (1 / 2) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (262569 / 2000000) (99621 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_115 : TightBoxCovered (3 / 4) (33 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 4) (33 / 64) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (293819 / 2000000) (20999 / 250000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_116 : TightBoxCovered (49 / 64) (33 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (49 / 64) (33 / 64) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (262569 / 2000000) (20999 / 250000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_117 : TightBoxCovered (3 / 4) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_113 using 1 <;> norm_num
  · convert tightQ3_114 using 1 <;> norm_num
  · convert tightQ3_115 using 1 <;> norm_num
  · convert tightQ3_116 using 1 <;> norm_num

theorem tightQ3_118 : TightBoxCovered (25 / 32) (1 / 2) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (1 / 2) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (231319 / 2000000) (99621 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_119 : TightBoxCovered (3 / 4) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (17 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (293819 / 2000000) (68371 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_120 : TightBoxCovered (25 / 32) (17 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (17 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (231319 / 2000000) (68371 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_121 : TightBoxCovered (3 / 4) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_117 using 1 <;> norm_num
  · convert tightQ3_118 using 1 <;> norm_num
  · convert tightQ3_119 using 1 <;> norm_num
  · convert tightQ3_120 using 1 <;> norm_num

theorem tightQ3_122 : TightBoxCovered (13 / 16) (1 / 2) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (1 / 2) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (168819 / 2000000) (99621 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_123 : TightBoxCovered (3 / 4) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 4) (9 / 16) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (293819 / 2000000) (37121 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_124 : TightBoxCovered (13 / 16) (9 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (9 / 16) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (168819 / 2000000) (37121 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_125 : TightBoxCovered (3 / 4) (1 / 2) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_121 using 1 <;> norm_num
  · convert tightQ3_122 using 1 <;> norm_num
  · convert tightQ3_123 using 1 <;> norm_num
  · convert tightQ3_124 using 1 <;> norm_num

theorem tightQ3_126 : TightBoxCovered (7 / 8) (1 / 2) (1 / 8) := by
  apply tightBoxCovered_leaf (7 / 8) (1 / 2) (1 / 8) (1793819 / 2000000) (599621 / 1000000) (206181 / 2000000) (99621 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_127 : TightBoxCovered (3 / 4) (5 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (5 / 8) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (304811 / 2000000) (62067 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_128 : TightBoxCovered (25 / 32) (5 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (5 / 8) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (231319 / 2000000) (56629 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_129 : TightBoxCovered (3 / 4) (21 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (21 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (304811 / 2000000) (30817 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_130 : TightBoxCovered (25 / 32) (21 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (21 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (231319 / 2000000) (87879 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_131 : TightBoxCovered (3 / 4) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_127 using 1 <;> norm_num
  · convert tightQ3_128 using 1 <;> norm_num
  · convert tightQ3_129 using 1 <;> norm_num
  · convert tightQ3_130 using 1 <;> norm_num

theorem tightQ3_132 : TightBoxCovered (13 / 16) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (5 / 8) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (168819 / 2000000) (87879 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_133 : TightBoxCovered (3 / 4) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (11 / 16) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (304811 / 2000000) (31683 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_134 : TightBoxCovered (25 / 32) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (11 / 16) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (231319 / 2000000) (119129 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_135 : TightBoxCovered (3 / 4) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (23 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (304811 / 2000000) (62933 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_136 : TightBoxCovered (25 / 32) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (23 / 32) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (80109 / 500000) (78991 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_137 : TightBoxCovered (101 / 128) (23 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (23 / 32) (1 / 128) (1793819 / 2000000) (599621 / 1000000) (107847 / 1000000) (253883 / 2000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_138 : TightBoxCovered (25 / 32) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (93 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (80109 / 500000) (11827 / 250000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_139 : TightBoxCovered (101 / 128) (93 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (101 / 128) (93 / 128) (1 / 256) (1257689 / 2000000) (687067 / 1000000) (656497 / 4000000) (173607 / 4000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_140 : TightBoxCovered (203 / 256) (93 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (203 / 256) (93 / 128) (1 / 256) (1793819 / 2000000) (599621 / 1000000) (415763 / 4000000) (523391 / 4000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_141 : TightBoxCovered (101 / 128) (187 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (101 / 128) (187 / 256) (1 / 512) (1257689 / 2000000) (687067 / 1000000) (1297369 / 8000000) (362839 / 8000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_142 : TightBoxCovered (405 / 512) (187 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (405 / 512) (187 / 256) (1 / 512) (1793819 / 2000000) (599621 / 1000000) (847151 / 8000000) (1062407 / 8000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_143 : TightBoxCovered (101 / 128) (375 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (101 / 128) (375 / 512) (1 / 512) (1257689 / 2000000) (687067 / 1000000) (1297369 / 8000000) (11827 / 250000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_144 : TightBoxCovered (405 / 512) (375 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (405 / 512) (375 / 512) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (2610363 / 16000000) (741303 / 16000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_145 : TightBoxCovered (811 / 1024) (375 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (811 / 1024) (375 / 512) (1 / 1024) (895009 / 1000000) (1734163 / 2000000) (1648269 / 16000000) (1077277 / 8000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_146 : TightBoxCovered (405 / 512) (751 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (405 / 512) (751 / 1024) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (2610363 / 16000000) (11827 / 250000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_147 : TightBoxCovered (811 / 1024) (751 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (811 / 1024) (751 / 1024) (1 / 1024) (895009 / 1000000) (1734163 / 2000000) (1648269 / 16000000) (2138929 / 16000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_148 : TightBoxCovered (405 / 512) (375 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ3_144 using 1 <;> norm_num
  · convert tightQ3_145 using 1 <;> norm_num
  · convert tightQ3_146 using 1 <;> norm_num
  · convert tightQ3_147 using 1 <;> norm_num

theorem tightQ3_149 : TightBoxCovered (101 / 128) (187 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ3_141 using 1 <;> norm_num
  · convert tightQ3_142 using 1 <;> norm_num
  · convert tightQ3_143 using 1 <;> norm_num
  · convert tightQ3_148 using 1 <;> norm_num

theorem tightQ3_150 : TightBoxCovered (203 / 256) (187 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (203 / 256) (187 / 256) (1 / 512) (1793819 / 2000000) (599621 / 1000000) (415763 / 4000000) (1062407 / 8000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_151 : TightBoxCovered (407 / 512) (187 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (407 / 512) (187 / 256) (1 / 512) (1793819 / 2000000) (599621 / 1000000) (815901 / 8000000) (1062407 / 8000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_152 : TightBoxCovered (203 / 256) (375 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (203 / 256) (375 / 512) (1 / 512) (895009 / 1000000) (1734163 / 2000000) (408161 / 4000000) (1077277 / 8000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_153 : TightBoxCovered (407 / 512) (375 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (407 / 512) (375 / 512) (1 / 512) (1793819 / 2000000) (599621 / 1000000) (815901 / 8000000) (67377 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_154 : TightBoxCovered (203 / 256) (187 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ3_150 using 1 <;> norm_num
  · convert tightQ3_151 using 1 <;> norm_num
  · convert tightQ3_152 using 1 <;> norm_num
  · convert tightQ3_153 using 1 <;> norm_num

theorem tightQ3_155 : TightBoxCovered (101 / 128) (93 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ3_139 using 1 <;> norm_num
  · convert tightQ3_140 using 1 <;> norm_num
  · convert tightQ3_149 using 1 <;> norm_num
  · convert tightQ3_154 using 1 <;> norm_num

theorem tightQ3_156 : TightBoxCovered (25 / 32) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_136 using 1 <;> norm_num
  · convert tightQ3_137 using 1 <;> norm_num
  · convert tightQ3_138 using 1 <;> norm_num
  · convert tightQ3_155 using 1 <;> norm_num

theorem tightQ3_157 : TightBoxCovered (51 / 64) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (23 / 32) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (200069 / 2000000) (67377 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_158 : TightBoxCovered (25 / 32) (47 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (47 / 64) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (80109 / 500000) (110241 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_159 : TightBoxCovered (101 / 128) (47 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (47 / 64) (1 / 128) (895009 / 1000000) (1734163 / 2000000) (211893 / 2000000) (265413 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_160 : TightBoxCovered (25 / 32) (95 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (95 / 128) (1 / 128) (895009 / 1000000) (1734163 / 2000000) (113759 / 1000000) (62447 / 500000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_161 : TightBoxCovered (101 / 128) (95 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (95 / 128) (1 / 128) (895009 / 1000000) (1734163 / 2000000) (211893 / 2000000) (62447 / 500000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_162 : TightBoxCovered (25 / 32) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_158 using 1 <;> norm_num
  · convert tightQ3_159 using 1 <;> norm_num
  · convert tightQ3_160 using 1 <;> norm_num
  · convert tightQ3_161 using 1 <;> norm_num

theorem tightQ3_163 : TightBoxCovered (51 / 64) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (47 / 64) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (49067 / 500000) (265413 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_164 : TightBoxCovered (25 / 32) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_156 using 1 <;> norm_num
  · convert tightQ3_157 using 1 <;> norm_num
  · convert tightQ3_162 using 1 <;> norm_num
  · convert tightQ3_163 using 1 <;> norm_num

theorem tightQ3_165 : TightBoxCovered (3 / 4) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_133 using 1 <;> norm_num
  · convert tightQ3_134 using 1 <;> norm_num
  · convert tightQ3_135 using 1 <;> norm_num
  · convert tightQ3_164 using 1 <;> norm_num

theorem tightQ3_166 : TightBoxCovered (13 / 16) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (13 / 16) (11 / 16) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (168819 / 2000000) (119129 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_167 : TightBoxCovered (27 / 32) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (27 / 32) (11 / 16) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (106319 / 2000000) (119129 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_168 : TightBoxCovered (13 / 16) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (13 / 16) (23 / 32) (1 / 32) (895009 / 1000000) (1734163 / 2000000) (82509 / 1000000) (296663 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_169 : TightBoxCovered (27 / 32) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (27 / 32) (23 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (106319 / 2000000) (150379 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_170 : TightBoxCovered (13 / 16) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_166 using 1 <;> norm_num
  · convert tightQ3_167 using 1 <;> norm_num
  · convert tightQ3_168 using 1 <;> norm_num
  · convert tightQ3_169 using 1 <;> norm_num

theorem tightQ3_171 : TightBoxCovered (3 / 4) (5 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_131 using 1 <;> norm_num
  · convert tightQ3_132 using 1 <;> norm_num
  · convert tightQ3_165 using 1 <;> norm_num
  · convert tightQ3_170 using 1 <;> norm_num

theorem tightQ3_172 : TightBoxCovered (7 / 8) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 8) (5 / 8) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (81181 / 2000000) (87879 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_173 : TightBoxCovered (15 / 16) (5 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (15 / 16) (5 / 8) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (206181 / 2000000) (87879 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_174 : TightBoxCovered (7 / 8) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 8) (11 / 16) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (81181 / 2000000) (150379 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_175 : TightBoxCovered (15 / 16) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 16) (11 / 16) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (143681 / 2000000) (119129 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_176 : TightBoxCovered (31 / 32) (11 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (31 / 32) (11 / 16) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (206181 / 2000000) (119129 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_177 : TightBoxCovered (15 / 16) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 16) (23 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (143681 / 2000000) (150379 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_178 : TightBoxCovered (31 / 32) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 32) (23 / 32) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (174931 / 2000000) (67377 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_179 : TightBoxCovered (63 / 64) (23 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (63 / 64) (23 / 32) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (206181 / 2000000) (67377 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_180 : TightBoxCovered (31 / 32) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 32) (47 / 64) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (44683 / 500000) (265413 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_181 : TightBoxCovered (63 / 64) (47 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (63 / 64) (47 / 64) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (104991 / 1000000) (265413 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_182 : TightBoxCovered (31 / 32) (23 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_178 using 1 <;> norm_num
  · convert tightQ3_179 using 1 <;> norm_num
  · convert tightQ3_180 using 1 <;> norm_num
  · convert tightQ3_181 using 1 <;> norm_num

theorem tightQ3_183 : TightBoxCovered (15 / 16) (11 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_175 using 1 <;> norm_num
  · convert tightQ3_176 using 1 <;> norm_num
  · convert tightQ3_177 using 1 <;> norm_num
  · convert tightQ3_182 using 1 <;> norm_num

theorem tightQ3_184 : TightBoxCovered (7 / 8) (5 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_172 using 1 <;> norm_num
  · convert tightQ3_173 using 1 <;> norm_num
  · convert tightQ3_174 using 1 <;> norm_num
  · convert tightQ3_183 using 1 <;> norm_num

theorem tightQ3_185 : TightBoxCovered (3 / 4) (1 / 2) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ3_125 using 1 <;> norm_num
  · convert tightQ3_126 using 1 <;> norm_num
  · convert tightQ3_171 using 1 <;> norm_num
  · convert tightQ3_184 using 1 <;> norm_num

theorem tightQ3_186 : TightBoxCovered (1 / 2) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (3 / 4) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (257689 / 2000000) (94183 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_187 : TightBoxCovered (17 / 32) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (3 / 4) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (94183 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_188 : TightBoxCovered (1 / 2) (25 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (25 / 32) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (257689 / 2000000) (6863 / 62500) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_189 : TightBoxCovered (33 / 64) (25 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (25 / 32) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (226439 / 2000000) (6863 / 62500) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_190 : TightBoxCovered (1 / 2) (51 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (51 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (298493 / 2000000) (64369 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_191 : TightBoxCovered (33 / 64) (51 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (51 / 64) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (226439 / 2000000) (125433 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_192 : TightBoxCovered (1 / 2) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_188 using 1 <;> norm_num
  · convert tightQ3_189 using 1 <;> norm_num
  · convert tightQ3_190 using 1 <;> norm_num
  · convert tightQ3_191 using 1 <;> norm_num

theorem tightQ3_193 : TightBoxCovered (17 / 32) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (25 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (125433 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_194 : TightBoxCovered (1 / 2) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_186 using 1 <;> norm_num
  · convert tightQ3_187 using 1 <;> norm_num
  · convert tightQ3_192 using 1 <;> norm_num
  · convert tightQ3_193 using 1 <;> norm_num

theorem tightQ3_195 : TightBoxCovered (9 / 16) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (3 / 4) (1 / 16) (1257689 / 2000000) (687067 / 1000000) (132689 / 2000000) (125433 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_196 : TightBoxCovered (1 / 2) (13 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (13 / 16) (1 / 64) (732757 / 2000000) (215311 / 250000) (298493 / 2000000) (6093 / 125000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_197 : TightBoxCovered (33 / 64) (13 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (13 / 16) (1 / 128) (732757 / 2000000) (215311 / 250000) (157059 / 1000000) (6093 / 125000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_198 : TightBoxCovered (67 / 128) (13 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (67 / 128) (13 / 16) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (105407 / 1000000) (266491 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_199 : TightBoxCovered (33 / 64) (105 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (105 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (157059 / 1000000) (81863 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_200 : TightBoxCovered (67 / 128) (105 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (67 / 128) (105 / 128) (1 / 128) (732757 / 2000000) (215311 / 250000) (329743 / 2000000) (81863 / 2000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_201 : TightBoxCovered (33 / 64) (13 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_197 using 1 <;> norm_num
  · convert tightQ3_198 using 1 <;> norm_num
  · convert tightQ3_199 using 1 <;> norm_num
  · convert tightQ3_200 using 1 <;> norm_num

theorem tightQ3_202 : TightBoxCovered (1 / 2) (53 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (53 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (298493 / 2000000) (33119 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_203 : TightBoxCovered (33 / 64) (53 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (53 / 64) (1 / 64) (732757 / 2000000) (215311 / 250000) (329743 / 2000000) (33119 / 1000000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_204 : TightBoxCovered (1 / 2) (13 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_196 using 1 <;> norm_num
  · convert tightQ3_201 using 1 <;> norm_num
  · convert tightQ3_202 using 1 <;> norm_num
  · convert tightQ3_203 using 1 <;> norm_num

theorem tightQ3_205 : TightBoxCovered (17 / 32) (13 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 32) (13 / 16) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (195189 / 2000000) (266491 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_206 : TightBoxCovered (69 / 128) (13 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (13 / 16) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (44891 / 500000) (266491 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_207 : TightBoxCovered (17 / 32) (105 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 32) (105 / 128) (1 / 128) (313399 / 500000) (954497 / 1000000) (23887 / 250000) (268369 / 2000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_208 : TightBoxCovered (69 / 128) (105 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (105 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (44891 / 500000) (70529 / 500000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_209 : TightBoxCovered (17 / 32) (13 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_205 using 1 <;> norm_num
  · convert tightQ3_206 using 1 <;> norm_num
  · convert tightQ3_207 using 1 <;> norm_num
  · convert tightQ3_208 using 1 <;> norm_num

theorem tightQ3_210 : TightBoxCovered (35 / 64) (13 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (13 / 16) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (163939 / 2000000) (70529 / 500000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_211 : TightBoxCovered (17 / 32) (53 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 32) (53 / 64) (1 / 64) (313399 / 500000) (954497 / 1000000) (23887 / 250000) (31593 / 250000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_212 : TightBoxCovered (35 / 64) (53 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (53 / 64) (1 / 64) (313399 / 500000) (954497 / 1000000) (79923 / 1000000) (31593 / 250000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_213 : TightBoxCovered (17 / 32) (13 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_209 using 1 <;> norm_num
  · convert tightQ3_210 using 1 <;> norm_num
  · convert tightQ3_211 using 1 <;> norm_num
  · convert tightQ3_212 using 1 <;> norm_num

theorem tightQ3_214 : TightBoxCovered (1 / 2) (27 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (27 / 32) (1 / 32) (732757 / 2000000) (215311 / 250000) (329743 / 2000000) (8747 / 500000) ⟨13, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_215 : TightBoxCovered (17 / 32) (27 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (27 / 32) (1 / 32) (313399 / 500000) (954497 / 1000000) (23887 / 250000) (110747 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_216 : TightBoxCovered (1 / 2) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_204 using 1 <;> norm_num
  · convert tightQ3_213 using 1 <;> norm_num
  · convert tightQ3_214 using 1 <;> norm_num
  · convert tightQ3_215 using 1 <;> norm_num

theorem tightQ3_217 : TightBoxCovered (9 / 16) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (13 / 16) (1 / 16) (313399 / 500000) (954497 / 1000000) (32149 / 500000) (141997 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_218 : TightBoxCovered (1 / 2) (3 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_194 using 1 <;> norm_num
  · convert tightQ3_195 using 1 <;> norm_num
  · convert tightQ3_216 using 1 <;> norm_num
  · convert tightQ3_217 using 1 <;> norm_num

theorem tightQ3_219 : TightBoxCovered (5 / 8) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 8) (3 / 4) (1 / 16) (1257689 / 2000000) (687067 / 1000000) (117311 / 2000000) (125433 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_220 : TightBoxCovered (11 / 16) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (3 / 4) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (179811 / 2000000) (94183 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_221 : TightBoxCovered (23 / 32) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (23 / 32) (3 / 4) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (242311 / 2000000) (94183 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_222 : TightBoxCovered (11 / 16) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (25 / 32) (1 / 32) (1257689 / 2000000) (687067 / 1000000) (179811 / 2000000) (125433 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_223 : TightBoxCovered (23 / 32) (25 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (25 / 32) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (211061 / 2000000) (6863 / 62500) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_224 : TightBoxCovered (47 / 64) (25 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (25 / 32) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (242311 / 2000000) (6863 / 62500) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_225 : TightBoxCovered (23 / 32) (51 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (51 / 64) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (211061 / 2000000) (125433 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_226 : TightBoxCovered (47 / 64) (51 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (51 / 64) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (113343 / 1000000) (235241 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_227 : TightBoxCovered (95 / 128) (51 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (51 / 64) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (242311 / 2000000) (235241 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_228 : TightBoxCovered (47 / 64) (103 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (103 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (113343 / 1000000) (125433 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_229 : TightBoxCovered (95 / 128) (103 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (103 / 128) (1 / 128) (895009 / 1000000) (1734163 / 2000000) (305643 / 2000000) (31197 / 500000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_230 : TightBoxCovered (47 / 64) (51 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_226 using 1 <;> norm_num
  · convert tightQ3_227 using 1 <;> norm_num
  · convert tightQ3_228 using 1 <;> norm_num
  · convert tightQ3_229 using 1 <;> norm_num

theorem tightQ3_231 : TightBoxCovered (23 / 32) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_223 using 1 <;> norm_num
  · convert tightQ3_224 using 1 <;> norm_num
  · convert tightQ3_225 using 1 <;> norm_num
  · convert tightQ3_230 using 1 <;> norm_num

theorem tightQ3_232 : TightBoxCovered (11 / 16) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_220 using 1 <;> norm_num
  · convert tightQ3_221 using 1 <;> norm_num
  · convert tightQ3_222 using 1 <;> norm_num
  · convert tightQ3_231 using 1 <;> norm_num

theorem tightQ3_233 : TightBoxCovered (5 / 8) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 8) (13 / 16) (1 / 16) (313399 / 500000) (954497 / 1000000) (30351 / 500000) (141997 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_234 : TightBoxCovered (11 / 16) (13 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (13 / 16) (1 / 32) (313399 / 500000) (954497 / 1000000) (5747 / 62500) (141997 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_235 : TightBoxCovered (23 / 32) (13 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) (13 / 16) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (48859 / 500000) (266491 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_236 : TightBoxCovered (93 / 128) (13 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (93 / 128) (13 / 16) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (211061 / 2000000) (266491 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_237 : TightBoxCovered (23 / 32) (105 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) (105 / 128) (1 / 128) (313399 / 500000) (954497 / 1000000) (199529 / 2000000) (268369 / 2000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_238 : TightBoxCovered (93 / 128) (105 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) (105 / 128) (1 / 256) (313399 / 500000) (954497 / 1000000) (414683 / 4000000) (268369 / 2000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_239 : TightBoxCovered (187 / 256) (105 / 128) (1 / 1024) := by
  apply tightBoxCovered_leaf (187 / 256) (105 / 128) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (1641613 / 16000000) (2147553 / 16000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_240 : TightBoxCovered (749 / 1024) (105 / 128) (1 / 1024) := by
  apply tightBoxCovered_leaf (749 / 1024) (105 / 128) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (828619 / 8000000) (2147553 / 16000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_241 : TightBoxCovered (187 / 256) (841 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (187 / 256) (841 / 1024) (1 / 1024) (1257689 / 2000000) (687067 / 1000000) (1641613 / 16000000) (1081589 / 8000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_242 : TightBoxCovered (749 / 1024) (841 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (749 / 1024) (841 / 1024) (1 / 1024) (895009 / 1000000) (1734163 / 2000000) (2617019 / 16000000) (732679 / 16000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_243 : TightBoxCovered (187 / 256) (105 / 128) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ3_239 using 1 <;> norm_num
  · convert tightQ3_240 using 1 <;> norm_num
  · convert tightQ3_241 using 1 <;> norm_num
  · convert tightQ3_242 using 1 <;> norm_num

theorem tightQ3_244 : TightBoxCovered (375 / 512) (105 / 128) (1 / 512) := by
  apply tightBoxCovered_leaf (375 / 512) (105 / 128) (1 / 512) (895009 / 1000000) (1734163 / 2000000) (1300697 / 8000000) (46769 / 1000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_245 : TightBoxCovered (187 / 256) (421 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (187 / 256) (421 / 512) (1 / 512) (313399 / 500000) (954497 / 1000000) (844991 / 8000000) (1057851 / 8000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_246 : TightBoxCovered (375 / 512) (421 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (375 / 512) (421 / 512) (1 / 512) (895009 / 1000000) (1734163 / 2000000) (1300697 / 8000000) (358527 / 8000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_247 : TightBoxCovered (187 / 256) (105 / 128) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ3_243 using 1 <;> norm_num
  · convert tightQ3_244 using 1 <;> norm_num
  · convert tightQ3_245 using 1 <;> norm_num
  · convert tightQ3_246 using 1 <;> norm_num

theorem tightQ3_248 : TightBoxCovered (93 / 128) (211 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) (211 / 256) (1 / 256) (313399 / 500000) (954497 / 1000000) (414683 / 4000000) (521113 / 4000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_249 : TightBoxCovered (187 / 256) (211 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (187 / 256) (211 / 256) (1 / 256) (313399 / 500000) (954497 / 1000000) (107577 / 1000000) (521113 / 4000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_250 : TightBoxCovered (93 / 128) (105 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ3_238 using 1 <;> norm_num
  · convert tightQ3_247 using 1 <;> norm_num
  · convert tightQ3_248 using 1 <;> norm_num
  · convert tightQ3_249 using 1 <;> norm_num

theorem tightQ3_251 : TightBoxCovered (23 / 32) (13 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_235 using 1 <;> norm_num
  · convert tightQ3_236 using 1 <;> norm_num
  · convert tightQ3_237 using 1 <;> norm_num
  · convert tightQ3_250 using 1 <;> norm_num

theorem tightQ3_252 : TightBoxCovered (47 / 64) (13 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (13 / 16) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (80317 / 500000) (109163 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_253 : TightBoxCovered (23 / 32) (53 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (53 / 64) (1 / 64) (313399 / 500000) (954497 / 1000000) (107577 / 1000000) (31593 / 250000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_254 : TightBoxCovered (47 / 64) (53 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (53 / 64) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (80317 / 500000) (77913 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_255 : TightBoxCovered (23 / 32) (13 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_251 using 1 <;> norm_num
  · convert tightQ3_252 using 1 <;> norm_num
  · convert tightQ3_253 using 1 <;> norm_num
  · convert tightQ3_254 using 1 <;> norm_num

theorem tightQ3_256 : TightBoxCovered (11 / 16) (27 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (27 / 32) (1 / 32) (313399 / 500000) (954497 / 1000000) (5747 / 62500) (110747 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_257 : TightBoxCovered (23 / 32) (27 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (23 / 32) (27 / 32) (1 / 32) (313399 / 500000) (954497 / 1000000) (61601 / 500000) (110747 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_258 : TightBoxCovered (11 / 16) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_234 using 1 <;> norm_num
  · convert tightQ3_255 using 1 <;> norm_num
  · convert tightQ3_256 using 1 <;> norm_num
  · convert tightQ3_257 using 1 <;> norm_num

theorem tightQ3_259 : TightBoxCovered (5 / 8) (3 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_219 using 1 <;> norm_num
  · convert tightQ3_232 using 1 <;> norm_num
  · convert tightQ3_233 using 1 <;> norm_num
  · convert tightQ3_258 using 1 <;> norm_num

theorem tightQ3_260 : TightBoxCovered (1 / 2) (7 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 2) (7 / 8) (1 / 8) (313399 / 500000) (954497 / 1000000) (63399 / 500000) (79497 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_261 : TightBoxCovered (5 / 8) (7 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (5 / 8) (7 / 8) (1 / 8) (313399 / 500000) (954497 / 1000000) (61601 / 500000) (79497 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_262 : TightBoxCovered (1 / 2) (3 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ3_218 using 1 <;> norm_num
  · convert tightQ3_259 using 1 <;> norm_num
  · convert tightQ3_260 using 1 <;> norm_num
  · convert tightQ3_261 using 1 <;> norm_num

theorem tightQ3_263 : TightBoxCovered (3 / 4) (3 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 4) (3 / 4) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (273561 / 2000000) (39279 / 500000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_264 : TightBoxCovered (49 / 64) (3 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (49 / 64) (3 / 4) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (144593 / 1000000) (141491 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_265 : TightBoxCovered (99 / 128) (3 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (99 / 128) (3 / 4) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (304811 / 2000000) (141491 / 2000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_266 : TightBoxCovered (49 / 64) (97 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (49 / 64) (97 / 128) (1 / 128) (1257689 / 2000000) (687067 / 1000000) (144593 / 1000000) (39279 / 500000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_267 : TightBoxCovered (99 / 128) (97 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (99 / 128) (97 / 128) (1 / 128) (895009 / 1000000) (1734163 / 2000000) (243143 / 2000000) (109269 / 1000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_268 : TightBoxCovered (49 / 64) (3 / 4) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_264 using 1 <;> norm_num
  · convert tightQ3_265 using 1 <;> norm_num
  · convert tightQ3_266 using 1 <;> norm_num
  · convert tightQ3_267 using 1 <;> norm_num

theorem tightQ3_269 : TightBoxCovered (3 / 4) (49 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 4) (49 / 64) (1 / 64) (1257689 / 2000000) (687067 / 1000000) (273561 / 2000000) (94183 / 1000000) ⟨10, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_270 : TightBoxCovered (49 / 64) (49 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (49 / 64) (49 / 64) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (16173 / 125000) (202913 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_271 : TightBoxCovered (3 / 4) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_263 using 1 <;> norm_num
  · convert tightQ3_268 using 1 <;> norm_num
  · convert tightQ3_269 using 1 <;> norm_num
  · convert tightQ3_270 using 1 <;> norm_num

theorem tightQ3_272 : TightBoxCovered (25 / 32) (3 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (3 / 4) (1 / 32) (895009 / 1000000) (1734163 / 2000000) (113759 / 1000000) (234163 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_273 : TightBoxCovered (3 / 4) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (25 / 32) (1 / 32) (895009 / 1000000) (1734163 / 2000000) (145009 / 1000000) (171663 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_274 : TightBoxCovered (25 / 32) (25 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (25 / 32) (1 / 32) (895009 / 1000000) (1734163 / 2000000) (113759 / 1000000) (171663 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_275 : TightBoxCovered (3 / 4) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_271 using 1 <;> norm_num
  · convert tightQ3_272 using 1 <;> norm_num
  · convert tightQ3_273 using 1 <;> norm_num
  · convert tightQ3_274 using 1 <;> norm_num

theorem tightQ3_276 : TightBoxCovered (13 / 16) (3 / 4) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (3 / 4) (1 / 16) (895009 / 1000000) (1734163 / 2000000) (82509 / 1000000) (234163 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_277 : TightBoxCovered (3 / 4) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 4) (13 / 16) (1 / 16) (895009 / 1000000) (1734163 / 2000000) (145009 / 1000000) (109163 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_278 : TightBoxCovered (13 / 16) (13 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (13 / 16) (1 / 16) (895009 / 1000000) (1734163 / 2000000) (82509 / 1000000) (109163 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_279 : TightBoxCovered (3 / 4) (3 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_275 using 1 <;> norm_num
  · convert tightQ3_276 using 1 <;> norm_num
  · convert tightQ3_277 using 1 <;> norm_num
  · convert tightQ3_278 using 1 <;> norm_num

theorem tightQ3_280 : TightBoxCovered (7 / 8) (3 / 4) (1 / 8) := by
  apply tightBoxCovered_leaf (7 / 8) (3 / 4) (1 / 8) (895009 / 1000000) (1734163 / 2000000) (104991 / 1000000) (234163 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_281 : TightBoxCovered (3 / 4) (7 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 4) (7 / 8) (1 / 16) (895009 / 1000000) (1734163 / 2000000) (145009 / 1000000) (140837 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_282 : TightBoxCovered (13 / 16) (7 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (7 / 8) (1 / 16) (895009 / 1000000) (1734163 / 2000000) (82509 / 1000000) (140837 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_283 : TightBoxCovered (3 / 4) (15 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (15 / 16) (1 / 32) (313399 / 500000) (954497 / 1000000) (38613 / 250000) (16997 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_284 : TightBoxCovered (25 / 32) (15 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (15 / 16) (1 / 32) (895009 / 1000000) (1734163 / 2000000) (113759 / 1000000) (203337 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_285 : TightBoxCovered (3 / 4) (31 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (31 / 32) (1 / 32) (313399 / 500000) (954497 / 1000000) (38613 / 250000) (45503 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_286 : TightBoxCovered (25 / 32) (31 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (25 / 32) (31 / 32) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (113759 / 1000000) (234587 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_287 : TightBoxCovered (51 / 64) (31 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (31 / 32) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (49067 / 500000) (234587 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_288 : TightBoxCovered (25 / 32) (63 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (63 / 64) (1 / 128) (313399 / 500000) (954497 / 1000000) (324529 / 2000000) (75381 / 2000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_289 : TightBoxCovered (101 / 128) (63 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (63 / 64) (1 / 128) (895009 / 1000000) (1734163 / 2000000) (211893 / 2000000) (62553 / 500000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_290 : TightBoxCovered (25 / 32) (127 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (127 / 128) (1 / 128) (313399 / 500000) (954497 / 1000000) (324529 / 2000000) (45503 / 1000000) ⟨14, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_291 : TightBoxCovered (101 / 128) (127 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (127 / 128) (1 / 128) (895009 / 1000000) (1734163 / 2000000) (211893 / 2000000) (265837 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_292 : TightBoxCovered (25 / 32) (63 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ3_288 using 1 <;> norm_num
  · convert tightQ3_289 using 1 <;> norm_num
  · convert tightQ3_290 using 1 <;> norm_num
  · convert tightQ3_291 using 1 <;> norm_num

theorem tightQ3_293 : TightBoxCovered (51 / 64) (63 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (63 / 64) (1 / 64) (895009 / 1000000) (1734163 / 2000000) (49067 / 500000) (265837 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_294 : TightBoxCovered (25 / 32) (31 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ3_286 using 1 <;> norm_num
  · convert tightQ3_287 using 1 <;> norm_num
  · convert tightQ3_292 using 1 <;> norm_num
  · convert tightQ3_293 using 1 <;> norm_num

theorem tightQ3_295 : TightBoxCovered (3 / 4) (15 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ3_283 using 1 <;> norm_num
  · convert tightQ3_284 using 1 <;> norm_num
  · convert tightQ3_285 using 1 <;> norm_num
  · convert tightQ3_294 using 1 <;> norm_num

theorem tightQ3_296 : TightBoxCovered (13 / 16) (15 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (15 / 16) (1 / 16) (895009 / 1000000) (1734163 / 2000000) (82509 / 1000000) (265837 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_297 : TightBoxCovered (3 / 4) (7 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ3_281 using 1 <;> norm_num
  · convert tightQ3_282 using 1 <;> norm_num
  · convert tightQ3_295 using 1 <;> norm_num
  · convert tightQ3_296 using 1 <;> norm_num

theorem tightQ3_298 : TightBoxCovered (7 / 8) (7 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (7 / 8) (7 / 8) (1 / 8) (895009 / 1000000) (1734163 / 2000000) (104991 / 1000000) (265837 / 2000000) ⟨15, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ3_299 : TightBoxCovered (3 / 4) (3 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ3_279 using 1 <;> norm_num
  · convert tightQ3_280 using 1 <;> norm_num
  · convert tightQ3_297 using 1 <;> norm_num
  · convert tightQ3_298 using 1 <;> norm_num

theorem tightQ3_300 : TightBoxCovered (1 / 2) (1 / 2) (1 / 2) := by
  apply tightBoxCovered_split
  · convert tightQ3_112 using 1 <;> norm_num
  · convert tightQ3_185 using 1 <;> norm_num
  · convert tightQ3_262 using 1 <;> norm_num
  · convert tightQ3_299 using 1 <;> norm_num

theorem tightQuadrant3 : TightBoxCovered (1 / 2) (1 / 2) (1/2) := tightQ3_300

end ElevenSquare
