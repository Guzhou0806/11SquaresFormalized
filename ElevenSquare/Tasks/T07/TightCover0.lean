import ElevenSquare.Tasks.T07.TightCoverChecks

/-! Untrusted generated dyadic tree, checked by Lean at every leaf. -/
namespace ElevenSquare
set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

theorem tightQ0_0 : TightBoxCovered 0 0 (1 / 8) := by
  apply tightBoxCovered_leaf 0 0 (1 / 8) (104991 / 1000000) (265837 / 2000000) (104991 / 1000000) (265837 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_1 : TightBoxCovered (1 / 8) 0 (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) 0 (1 / 16) (104991 / 1000000) (265837 / 2000000) (82509 / 1000000) (265837 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_2 : TightBoxCovered (3 / 16) 0 (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) 0 (1 / 64) (104991 / 1000000) (265837 / 2000000) (49067 / 500000) (265837 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_3 : TightBoxCovered (13 / 64) 0 (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) 0 (1 / 128) (104991 / 1000000) (265837 / 2000000) (211893 / 2000000) (265837 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_4 : TightBoxCovered (27 / 128) 0 (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) 0 (1 / 128) (186601 / 500000) (45503 / 1000000) (324529 / 2000000) (45503 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_5 : TightBoxCovered (13 / 64) (1 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (1 / 128) (1 / 128) (104991 / 1000000) (265837 / 2000000) (211893 / 2000000) (62553 / 500000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_6 : TightBoxCovered (27 / 128) (1 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (1 / 128) (1 / 128) (104991 / 1000000) (265837 / 2000000) (113759 / 1000000) (62553 / 500000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_7 : TightBoxCovered (13 / 64) 0 (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_3 using 1 <;> norm_num
  · convert tightQ0_4 using 1 <;> norm_num
  · convert tightQ0_5 using 1 <;> norm_num
  · convert tightQ0_6 using 1 <;> norm_num

theorem tightQ0_8 : TightBoxCovered (3 / 16) (1 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) (1 / 64) (1 / 64) (104991 / 1000000) (265837 / 2000000) (49067 / 500000) (234587 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_9 : TightBoxCovered (13 / 64) (1 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (13 / 64) (1 / 64) (1 / 64) (104991 / 1000000) (265837 / 2000000) (113759 / 1000000) (234587 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_10 : TightBoxCovered (3 / 16) 0 (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_2 using 1 <;> norm_num
  · convert tightQ0_7 using 1 <;> norm_num
  · convert tightQ0_8 using 1 <;> norm_num
  · convert tightQ0_9 using 1 <;> norm_num

theorem tightQ0_11 : TightBoxCovered (7 / 32) 0 (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) 0 (1 / 32) (186601 / 500000) (45503 / 1000000) (38613 / 250000) (45503 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_12 : TightBoxCovered (3 / 16) (1 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (1 / 32) (1 / 32) (104991 / 1000000) (265837 / 2000000) (113759 / 1000000) (203337 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_13 : TightBoxCovered (7 / 32) (1 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (1 / 32) (1 / 32) (186601 / 500000) (45503 / 1000000) (38613 / 250000) (16997 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_14 : TightBoxCovered (3 / 16) 0 (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_10 using 1 <;> norm_num
  · convert tightQ0_11 using 1 <;> norm_num
  · convert tightQ0_12 using 1 <;> norm_num
  · convert tightQ0_13 using 1 <;> norm_num

theorem tightQ0_15 : TightBoxCovered (1 / 8) (1 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (1 / 16) (1 / 16) (104991 / 1000000) (265837 / 2000000) (82509 / 1000000) (140837 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_16 : TightBoxCovered (3 / 16) (1 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 16) (1 / 16) (1 / 16) (104991 / 1000000) (265837 / 2000000) (145009 / 1000000) (140837 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_17 : TightBoxCovered (1 / 8) 0 (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_1 using 1 <;> norm_num
  · convert tightQ0_14 using 1 <;> norm_num
  · convert tightQ0_15 using 1 <;> norm_num
  · convert tightQ0_16 using 1 <;> norm_num

theorem tightQ0_18 : TightBoxCovered 0 (1 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf 0 (1 / 8) (1 / 8) (104991 / 1000000) (265837 / 2000000) (104991 / 1000000) (234163 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_19 : TightBoxCovered (1 / 8) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (1 / 8) (1 / 16) (104991 / 1000000) (265837 / 2000000) (82509 / 1000000) (109163 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_20 : TightBoxCovered (3 / 16) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 16) (1 / 8) (1 / 16) (104991 / 1000000) (265837 / 2000000) (145009 / 1000000) (109163 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_21 : TightBoxCovered (1 / 8) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (3 / 16) (1 / 16) (104991 / 1000000) (265837 / 2000000) (82509 / 1000000) (234163 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_22 : TightBoxCovered (3 / 16) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (3 / 16) (1 / 32) (104991 / 1000000) (265837 / 2000000) (113759 / 1000000) (171663 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_23 : TightBoxCovered (7 / 32) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (3 / 16) (1 / 32) (104991 / 1000000) (265837 / 2000000) (145009 / 1000000) (171663 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_24 : TightBoxCovered (3 / 16) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (7 / 32) (1 / 32) (104991 / 1000000) (265837 / 2000000) (113759 / 1000000) (234163 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_25 : TightBoxCovered (7 / 32) (7 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 32) (7 / 32) (1 / 64) (104991 / 1000000) (265837 / 2000000) (16173 / 125000) (202913 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_26 : TightBoxCovered (15 / 64) (7 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 64) (7 / 32) (1 / 64) (742311 / 2000000) (312933 / 1000000) (273561 / 2000000) (94183 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_27 : TightBoxCovered (7 / 32) (15 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (7 / 32) (15 / 64) (1 / 128) (104991 / 1000000) (265837 / 2000000) (243143 / 2000000) (109269 / 1000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_28 : TightBoxCovered (29 / 128) (15 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 128) (15 / 64) (1 / 128) (104991 / 1000000) (265837 / 2000000) (16173 / 125000) (109269 / 1000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_29 : TightBoxCovered (7 / 32) (31 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (7 / 32) (31 / 128) (1 / 128) (104991 / 1000000) (265837 / 2000000) (243143 / 2000000) (234163 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_30 : TightBoxCovered (29 / 128) (31 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 128) (31 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (144593 / 1000000) (141491 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_31 : TightBoxCovered (7 / 32) (15 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_27 using 1 <;> norm_num
  · convert tightQ0_28 using 1 <;> norm_num
  · convert tightQ0_29 using 1 <;> norm_num
  · convert tightQ0_30 using 1 <;> norm_num

theorem tightQ0_32 : TightBoxCovered (15 / 64) (15 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 64) (15 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (273561 / 2000000) (39279 / 500000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_33 : TightBoxCovered (7 / 32) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_25 using 1 <;> norm_num
  · convert tightQ0_26 using 1 <;> norm_num
  · convert tightQ0_31 using 1 <;> norm_num
  · convert tightQ0_32 using 1 <;> norm_num

theorem tightQ0_34 : TightBoxCovered (3 / 16) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_22 using 1 <;> norm_num
  · convert tightQ0_23 using 1 <;> norm_num
  · convert tightQ0_24 using 1 <;> norm_num
  · convert tightQ0_33 using 1 <;> norm_num

theorem tightQ0_35 : TightBoxCovered (1 / 8) (1 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_19 using 1 <;> norm_num
  · convert tightQ0_20 using 1 <;> norm_num
  · convert tightQ0_21 using 1 <;> norm_num
  · convert tightQ0_34 using 1 <;> norm_num

theorem tightQ0_36 : TightBoxCovered 0 0 (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ0_0 using 1 <;> norm_num
  · convert tightQ0_17 using 1 <;> norm_num
  · convert tightQ0_18 using 1 <;> norm_num
  · convert tightQ0_35 using 1 <;> norm_num

theorem tightQ0_37 : TightBoxCovered (1 / 4) 0 (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 4) 0 (1 / 8) (186601 / 500000) (45503 / 1000000) (61601 / 500000) (79497 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_38 : TightBoxCovered (3 / 8) 0 (1 / 8) := by
  apply tightBoxCovered_leaf (3 / 8) 0 (1 / 8) (186601 / 500000) (45503 / 1000000) (63399 / 500000) (79497 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_39 : TightBoxCovered (1 / 4) (1 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 4) (1 / 8) (1 / 32) (186601 / 500000) (45503 / 1000000) (61601 / 500000) (110747 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_40 : TightBoxCovered (9 / 32) (1 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (1 / 8) (1 / 32) (186601 / 500000) (45503 / 1000000) (5747 / 62500) (110747 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_41 : TightBoxCovered (1 / 4) (5 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (5 / 32) (1 / 64) (104991 / 1000000) (265837 / 2000000) (80317 / 500000) (77913 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_42 : TightBoxCovered (17 / 64) (5 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (5 / 32) (1 / 64) (186601 / 500000) (45503 / 1000000) (107577 / 1000000) (31593 / 250000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_43 : TightBoxCovered (1 / 4) (11 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (11 / 64) (1 / 64) (104991 / 1000000) (265837 / 2000000) (80317 / 500000) (109163 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_44 : TightBoxCovered (17 / 64) (11 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 64) (11 / 64) (1 / 256) (186601 / 500000) (45503 / 1000000) (107577 / 1000000) (521113 / 4000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_45 : TightBoxCovered (69 / 256) (11 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (11 / 64) (1 / 256) (186601 / 500000) (45503 / 1000000) (414683 / 4000000) (521113 / 4000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_46 : TightBoxCovered (17 / 64) (45 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 64) (45 / 256) (1 / 512) (104991 / 1000000) (265837 / 2000000) (1300697 / 8000000) (358527 / 8000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_47 : TightBoxCovered (137 / 512) (45 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 512) (45 / 256) (1 / 512) (186601 / 500000) (45503 / 1000000) (844991 / 8000000) (1057851 / 8000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_48 : TightBoxCovered (17 / 64) (91 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 64) (91 / 512) (1 / 512) (104991 / 1000000) (265837 / 2000000) (1300697 / 8000000) (46769 / 1000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_49 : TightBoxCovered (137 / 512) (91 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (137 / 512) (91 / 512) (1 / 1024) (104991 / 1000000) (265837 / 2000000) (2617019 / 16000000) (732679 / 16000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_50 : TightBoxCovered (275 / 1024) (91 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (275 / 1024) (91 / 512) (1 / 1024) (186601 / 500000) (45503 / 1000000) (1674357 / 16000000) (2131327 / 16000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_51 : TightBoxCovered (137 / 512) (183 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (137 / 512) (183 / 1024) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (828619 / 8000000) (2147553 / 16000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_52 : TightBoxCovered (275 / 1024) (183 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (275 / 1024) (183 / 1024) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (1641613 / 16000000) (2147553 / 16000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_53 : TightBoxCovered (137 / 512) (91 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ0_49 using 1 <;> norm_num
  · convert tightQ0_50 using 1 <;> norm_num
  · convert tightQ0_51 using 1 <;> norm_num
  · convert tightQ0_52 using 1 <;> norm_num

theorem tightQ0_54 : TightBoxCovered (17 / 64) (45 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ0_46 using 1 <;> norm_num
  · convert tightQ0_47 using 1 <;> norm_num
  · convert tightQ0_48 using 1 <;> norm_num
  · convert tightQ0_53 using 1 <;> norm_num

theorem tightQ0_55 : TightBoxCovered (69 / 256) (45 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (45 / 256) (1 / 256) (186601 / 500000) (45503 / 1000000) (414683 / 4000000) (268369 / 2000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_56 : TightBoxCovered (17 / 64) (11 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ0_44 using 1 <;> norm_num
  · convert tightQ0_45 using 1 <;> norm_num
  · convert tightQ0_54 using 1 <;> norm_num
  · convert tightQ0_55 using 1 <;> norm_num

theorem tightQ0_57 : TightBoxCovered (35 / 128) (11 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (11 / 64) (1 / 128) (186601 / 500000) (45503 / 1000000) (199529 / 2000000) (268369 / 2000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_58 : TightBoxCovered (17 / 64) (23 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 64) (23 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (211061 / 2000000) (266491 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_59 : TightBoxCovered (35 / 128) (23 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (23 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (48859 / 500000) (266491 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_60 : TightBoxCovered (17 / 64) (11 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_56 using 1 <;> norm_num
  · convert tightQ0_57 using 1 <;> norm_num
  · convert tightQ0_58 using 1 <;> norm_num
  · convert tightQ0_59 using 1 <;> norm_num

theorem tightQ0_61 : TightBoxCovered (1 / 4) (5 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_41 using 1 <;> norm_num
  · convert tightQ0_42 using 1 <;> norm_num
  · convert tightQ0_43 using 1 <;> norm_num
  · convert tightQ0_60 using 1 <;> norm_num

theorem tightQ0_62 : TightBoxCovered (9 / 32) (5 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (5 / 32) (1 / 32) (186601 / 500000) (45503 / 1000000) (5747 / 62500) (141997 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_63 : TightBoxCovered (1 / 4) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_39 using 1 <;> norm_num
  · convert tightQ0_40 using 1 <;> norm_num
  · convert tightQ0_61 using 1 <;> norm_num
  · convert tightQ0_62 using 1 <;> norm_num

theorem tightQ0_64 : TightBoxCovered (5 / 16) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 16) (1 / 8) (1 / 16) (186601 / 500000) (45503 / 1000000) (30351 / 500000) (141997 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_65 : TightBoxCovered (1 / 4) (3 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (3 / 16) (1 / 128) (104991 / 1000000) (265837 / 2000000) (305643 / 2000000) (31197 / 500000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_66 : TightBoxCovered (33 / 128) (3 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (3 / 16) (1 / 128) (742311 / 2000000) (312933 / 1000000) (113343 / 1000000) (125433 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_67 : TightBoxCovered (1 / 4) (25 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (25 / 128) (1 / 128) (104991 / 1000000) (265837 / 2000000) (305643 / 2000000) (140413 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_68 : TightBoxCovered (33 / 128) (25 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (25 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (113343 / 1000000) (235241 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_69 : TightBoxCovered (1 / 4) (3 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_65 using 1 <;> norm_num
  · convert tightQ0_66 using 1 <;> norm_num
  · convert tightQ0_67 using 1 <;> norm_num
  · convert tightQ0_68 using 1 <;> norm_num

theorem tightQ0_70 : TightBoxCovered (17 / 64) (3 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (3 / 16) (1 / 64) (742311 / 2000000) (312933 / 1000000) (211061 / 2000000) (125433 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_71 : TightBoxCovered (1 / 4) (13 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (13 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (242311 / 2000000) (6863 / 62500) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_72 : TightBoxCovered (17 / 64) (13 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (13 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (211061 / 2000000) (6863 / 62500) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_73 : TightBoxCovered (1 / 4) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_69 using 1 <;> norm_num
  · convert tightQ0_70 using 1 <;> norm_num
  · convert tightQ0_71 using 1 <;> norm_num
  · convert tightQ0_72 using 1 <;> norm_num

theorem tightQ0_74 : TightBoxCovered (9 / 32) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (3 / 16) (1 / 32) (742311 / 2000000) (312933 / 1000000) (179811 / 2000000) (125433 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_75 : TightBoxCovered (1 / 4) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 4) (7 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (242311 / 2000000) (94183 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_76 : TightBoxCovered (9 / 32) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (7 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (179811 / 2000000) (94183 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_77 : TightBoxCovered (1 / 4) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_73 using 1 <;> norm_num
  · convert tightQ0_74 using 1 <;> norm_num
  · convert tightQ0_75 using 1 <;> norm_num
  · convert tightQ0_76 using 1 <;> norm_num

theorem tightQ0_78 : TightBoxCovered (5 / 16) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 16) (3 / 16) (1 / 16) (742311 / 2000000) (312933 / 1000000) (117311 / 2000000) (125433 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_79 : TightBoxCovered (1 / 4) (1 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_63 using 1 <;> norm_num
  · convert tightQ0_64 using 1 <;> norm_num
  · convert tightQ0_77 using 1 <;> norm_num
  · convert tightQ0_78 using 1 <;> norm_num

theorem tightQ0_80 : TightBoxCovered (3 / 8) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (1 / 8) (1 / 16) (186601 / 500000) (45503 / 1000000) (32149 / 500000) (141997 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_81 : TightBoxCovered (7 / 16) (1 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (1 / 8) (1 / 32) (186601 / 500000) (45503 / 1000000) (23887 / 250000) (110747 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_82 : TightBoxCovered (15 / 32) (1 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (1 / 8) (1 / 32) (186601 / 500000) (45503 / 1000000) (63399 / 500000) (110747 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_83 : TightBoxCovered (7 / 16) (5 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (5 / 32) (1 / 64) (186601 / 500000) (45503 / 1000000) (79923 / 1000000) (31593 / 250000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_84 : TightBoxCovered (29 / 64) (5 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (29 / 64) (5 / 32) (1 / 64) (186601 / 500000) (45503 / 1000000) (23887 / 250000) (31593 / 250000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_85 : TightBoxCovered (7 / 16) (11 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (11 / 64) (1 / 64) (186601 / 500000) (45503 / 1000000) (79923 / 1000000) (141997 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_86 : TightBoxCovered (29 / 64) (11 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (11 / 64) (1 / 128) (186601 / 500000) (45503 / 1000000) (175471 / 2000000) (268369 / 2000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_87 : TightBoxCovered (59 / 128) (11 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (59 / 128) (11 / 64) (1 / 128) (186601 / 500000) (45503 / 1000000) (23887 / 250000) (268369 / 2000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_88 : TightBoxCovered (29 / 64) (23 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (23 / 128) (1 / 128) (186601 / 500000) (45503 / 1000000) (175471 / 2000000) (141997 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_89 : TightBoxCovered (59 / 128) (23 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (59 / 128) (23 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (266491 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_90 : TightBoxCovered (29 / 64) (11 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_86 using 1 <;> norm_num
  · convert tightQ0_87 using 1 <;> norm_num
  · convert tightQ0_88 using 1 <;> norm_num
  · convert tightQ0_89 using 1 <;> norm_num

theorem tightQ0_91 : TightBoxCovered (7 / 16) (5 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_83 using 1 <;> norm_num
  · convert tightQ0_84 using 1 <;> norm_num
  · convert tightQ0_85 using 1 <;> norm_num
  · convert tightQ0_90 using 1 <;> norm_num

theorem tightQ0_92 : TightBoxCovered (15 / 32) (5 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (5 / 32) (1 / 64) (186601 / 500000) (45503 / 1000000) (111173 / 1000000) (31593 / 250000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_93 : TightBoxCovered (31 / 64) (5 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (5 / 32) (1 / 64) (1267243 / 2000000) (34689 / 250000) (298493 / 2000000) (33119 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_94 : TightBoxCovered (15 / 32) (11 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 32) (11 / 64) (1 / 128) (186601 / 500000) (45503 / 1000000) (206721 / 2000000) (268369 / 2000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_95 : TightBoxCovered (61 / 128) (11 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (11 / 64) (1 / 128) (1267243 / 2000000) (34689 / 250000) (157059 / 1000000) (81863 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_96 : TightBoxCovered (15 / 32) (23 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 32) (23 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (105407 / 1000000) (266491 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_97 : TightBoxCovered (61 / 128) (23 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (23 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (157059 / 1000000) (6093 / 125000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_98 : TightBoxCovered (15 / 32) (11 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_94 using 1 <;> norm_num
  · convert tightQ0_95 using 1 <;> norm_num
  · convert tightQ0_96 using 1 <;> norm_num
  · convert tightQ0_97 using 1 <;> norm_num

theorem tightQ0_99 : TightBoxCovered (31 / 64) (11 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (11 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (298493 / 2000000) (6093 / 125000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_100 : TightBoxCovered (15 / 32) (5 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_92 using 1 <;> norm_num
  · convert tightQ0_93 using 1 <;> norm_num
  · convert tightQ0_98 using 1 <;> norm_num
  · convert tightQ0_99 using 1 <;> norm_num

theorem tightQ0_101 : TightBoxCovered (7 / 16) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_81 using 1 <;> norm_num
  · convert tightQ0_82 using 1 <;> norm_num
  · convert tightQ0_91 using 1 <;> norm_num
  · convert tightQ0_100 using 1 <;> norm_num

theorem tightQ0_102 : TightBoxCovered (3 / 8) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (3 / 16) (1 / 16) (742311 / 2000000) (312933 / 1000000) (132689 / 2000000) (125433 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_103 : TightBoxCovered (7 / 16) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (3 / 16) (1 / 32) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (125433 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_104 : TightBoxCovered (15 / 32) (3 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (3 / 16) (1 / 64) (742311 / 2000000) (312933 / 1000000) (226439 / 2000000) (125433 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_105 : TightBoxCovered (31 / 64) (3 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (3 / 16) (1 / 64) (1267243 / 2000000) (34689 / 250000) (298493 / 2000000) (64369 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_106 : TightBoxCovered (15 / 32) (13 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (13 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (226439 / 2000000) (6863 / 62500) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_107 : TightBoxCovered (31 / 64) (13 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (13 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (298493 / 2000000) (39997 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_108 : TightBoxCovered (15 / 32) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_104 using 1 <;> norm_num
  · convert tightQ0_105 using 1 <;> norm_num
  · convert tightQ0_106 using 1 <;> norm_num
  · convert tightQ0_107 using 1 <;> norm_num

theorem tightQ0_109 : TightBoxCovered (7 / 16) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (7 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (94183 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_110 : TightBoxCovered (15 / 32) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (7 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (257689 / 2000000) (94183 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_111 : TightBoxCovered (7 / 16) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_103 using 1 <;> norm_num
  · convert tightQ0_108 using 1 <;> norm_num
  · convert tightQ0_109 using 1 <;> norm_num
  · convert tightQ0_110 using 1 <;> norm_num

theorem tightQ0_112 : TightBoxCovered (3 / 8) (1 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_80 using 1 <;> norm_num
  · convert tightQ0_101 using 1 <;> norm_num
  · convert tightQ0_102 using 1 <;> norm_num
  · convert tightQ0_111 using 1 <;> norm_num

theorem tightQ0_113 : TightBoxCovered (1 / 4) 0 (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ0_37 using 1 <;> norm_num
  · convert tightQ0_38 using 1 <;> norm_num
  · convert tightQ0_79 using 1 <;> norm_num
  · convert tightQ0_112 using 1 <;> norm_num

theorem tightQ0_114 : TightBoxCovered 0 (1 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf 0 (1 / 4) (1 / 64) (104991 / 1000000) (265837 / 2000000) (104991 / 1000000) (265413 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_115 : TightBoxCovered (1 / 64) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 64) (1 / 4) (1 / 64) (104991 / 1000000) (265837 / 2000000) (44683 / 500000) (265413 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_116 : TightBoxCovered 0 (17 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf 0 (17 / 64) (1 / 64) (206181 / 2000000) (400379 / 1000000) (206181 / 2000000) (67377 / 500000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_117 : TightBoxCovered (1 / 64) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 64) (17 / 64) (1 / 64) (206181 / 2000000) (400379 / 1000000) (174931 / 2000000) (67377 / 500000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_118 : TightBoxCovered 0 (1 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_114 using 1 <;> norm_num
  · convert tightQ0_115 using 1 <;> norm_num
  · convert tightQ0_116 using 1 <;> norm_num
  · convert tightQ0_117 using 1 <;> norm_num

theorem tightQ0_119 : TightBoxCovered (1 / 32) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 32) (1 / 4) (1 / 32) (104991 / 1000000) (265837 / 2000000) (73741 / 1000000) (296663 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_120 : TightBoxCovered 0 (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf 0 (9 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (206181 / 2000000) (119129 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_121 : TightBoxCovered (1 / 32) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 32) (9 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (143681 / 2000000) (119129 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_122 : TightBoxCovered 0 (1 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_118 using 1 <;> norm_num
  · convert tightQ0_119 using 1 <;> norm_num
  · convert tightQ0_120 using 1 <;> norm_num
  · convert tightQ0_121 using 1 <;> norm_num

theorem tightQ0_123 : TightBoxCovered (1 / 16) (1 / 4) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 16) (1 / 4) (1 / 16) (206181 / 2000000) (400379 / 1000000) (81181 / 2000000) (150379 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_124 : TightBoxCovered 0 (5 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf 0 (5 / 16) (1 / 16) (206181 / 2000000) (400379 / 1000000) (206181 / 2000000) (87879 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_125 : TightBoxCovered (1 / 16) (5 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 16) (5 / 16) (1 / 16) (206181 / 2000000) (400379 / 1000000) (81181 / 2000000) (87879 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_126 : TightBoxCovered 0 (1 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_122 using 1 <;> norm_num
  · convert tightQ0_123 using 1 <;> norm_num
  · convert tightQ0_124 using 1 <;> norm_num
  · convert tightQ0_125 using 1 <;> norm_num

theorem tightQ0_127 : TightBoxCovered (1 / 8) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 8) (1 / 4) (1 / 32) (104991 / 1000000) (265837 / 2000000) (51259 / 1000000) (296663 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_128 : TightBoxCovered (5 / 32) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 32) (1 / 4) (1 / 32) (104991 / 1000000) (265837 / 2000000) (82509 / 1000000) (296663 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_129 : TightBoxCovered (1 / 8) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 8) (9 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (106319 / 2000000) (119129 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_130 : TightBoxCovered (5 / 32) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 32) (9 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (168819 / 2000000) (119129 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_131 : TightBoxCovered (1 / 8) (1 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_127 using 1 <;> norm_num
  · convert tightQ0_128 using 1 <;> norm_num
  · convert tightQ0_129 using 1 <;> norm_num
  · convert tightQ0_130 using 1 <;> norm_num

theorem tightQ0_132 : TightBoxCovered (3 / 16) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) (1 / 4) (1 / 64) (104991 / 1000000) (265837 / 2000000) (49067 / 500000) (265413 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_133 : TightBoxCovered (13 / 64) (1 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (1 / 4) (1 / 128) (104991 / 1000000) (265837 / 2000000) (211893 / 2000000) (62447 / 500000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_134 : TightBoxCovered (27 / 128) (1 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (1 / 4) (1 / 128) (104991 / 1000000) (265837 / 2000000) (113759 / 1000000) (62447 / 500000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_135 : TightBoxCovered (13 / 64) (33 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (33 / 128) (1 / 128) (104991 / 1000000) (265837 / 2000000) (211893 / 2000000) (265413 / 2000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_136 : TightBoxCovered (27 / 128) (33 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (33 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (80109 / 500000) (110241 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_137 : TightBoxCovered (13 / 64) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_133 using 1 <;> norm_num
  · convert tightQ0_134 using 1 <;> norm_num
  · convert tightQ0_135 using 1 <;> norm_num
  · convert tightQ0_136 using 1 <;> norm_num

theorem tightQ0_138 : TightBoxCovered (3 / 16) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 16) (17 / 64) (1 / 64) (206181 / 2000000) (400379 / 1000000) (200069 / 2000000) (67377 / 500000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_139 : TightBoxCovered (13 / 64) (17 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (13 / 64) (17 / 64) (1 / 512) (104991 / 1000000) (265837 / 2000000) (800697 / 8000000) (1077277 / 8000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_140 : TightBoxCovered (105 / 512) (17 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (105 / 512) (17 / 64) (1 / 512) (104991 / 1000000) (265837 / 2000000) (408161 / 4000000) (1077277 / 8000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_141 : TightBoxCovered (13 / 64) (137 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (13 / 64) (137 / 512) (1 / 512) (104991 / 1000000) (265837 / 2000000) (800697 / 8000000) (546451 / 4000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_142 : TightBoxCovered (105 / 512) (137 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (105 / 512) (137 / 512) (1 / 512) (206181 / 2000000) (400379 / 1000000) (415763 / 4000000) (1062407 / 8000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_143 : TightBoxCovered (13 / 64) (17 / 64) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ0_139 using 1 <;> norm_num
  · convert tightQ0_140 using 1 <;> norm_num
  · convert tightQ0_141 using 1 <;> norm_num
  · convert tightQ0_142 using 1 <;> norm_num

theorem tightQ0_144 : TightBoxCovered (53 / 256) (17 / 64) (1 / 1024) := by
  apply tightBoxCovered_leaf (53 / 256) (17 / 64) (1 / 1024) (104991 / 1000000) (265837 / 2000000) (1648269 / 16000000) (2138929 / 16000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_145 : TightBoxCovered (213 / 1024) (17 / 64) (1 / 1024) := by
  apply tightBoxCovered_leaf (213 / 1024) (17 / 64) (1 / 1024) (104991 / 1000000) (265837 / 2000000) (831947 / 8000000) (2138929 / 16000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_146 : TightBoxCovered (53 / 256) (273 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (53 / 256) (273 / 1024) (1 / 1024) (104991 / 1000000) (265837 / 2000000) (1648269 / 16000000) (1077277 / 8000000) ⟨0, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_147 : TightBoxCovered (213 / 1024) (273 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (213 / 1024) (273 / 1024) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (2610363 / 16000000) (741303 / 16000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_148 : TightBoxCovered (53 / 256) (17 / 64) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ0_144 using 1 <;> norm_num
  · convert tightQ0_145 using 1 <;> norm_num
  · convert tightQ0_146 using 1 <;> norm_num
  · convert tightQ0_147 using 1 <;> norm_num

theorem tightQ0_149 : TightBoxCovered (107 / 512) (17 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (107 / 512) (17 / 64) (1 / 512) (742311 / 2000000) (312933 / 1000000) (1297369 / 8000000) (11827 / 250000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_150 : TightBoxCovered (53 / 256) (137 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (53 / 256) (137 / 512) (1 / 512) (206181 / 2000000) (400379 / 1000000) (847151 / 8000000) (1062407 / 8000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_151 : TightBoxCovered (107 / 512) (137 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (107 / 512) (137 / 512) (1 / 512) (742311 / 2000000) (312933 / 1000000) (1297369 / 8000000) (362839 / 8000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_152 : TightBoxCovered (53 / 256) (17 / 64) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ0_148 using 1 <;> norm_num
  · convert tightQ0_149 using 1 <;> norm_num
  · convert tightQ0_150 using 1 <;> norm_num
  · convert tightQ0_151 using 1 <;> norm_num

theorem tightQ0_153 : TightBoxCovered (13 / 64) (69 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (13 / 64) (69 / 256) (1 / 256) (206181 / 2000000) (400379 / 1000000) (415763 / 4000000) (523391 / 4000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_154 : TightBoxCovered (53 / 256) (69 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (53 / 256) (69 / 256) (1 / 256) (206181 / 2000000) (400379 / 1000000) (107847 / 1000000) (523391 / 4000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_155 : TightBoxCovered (13 / 64) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ0_143 using 1 <;> norm_num
  · convert tightQ0_152 using 1 <;> norm_num
  · convert tightQ0_153 using 1 <;> norm_num
  · convert tightQ0_154 using 1 <;> norm_num

theorem tightQ0_156 : TightBoxCovered (27 / 128) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (17 / 64) (1 / 128) (742311 / 2000000) (312933 / 1000000) (80109 / 500000) (11827 / 250000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_157 : TightBoxCovered (13 / 64) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (13 / 64) (35 / 128) (1 / 128) (206181 / 2000000) (400379 / 1000000) (107847 / 1000000) (253883 / 2000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_158 : TightBoxCovered (27 / 128) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (27 / 128) (35 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (80109 / 500000) (78991 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_159 : TightBoxCovered (13 / 64) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_155 using 1 <;> norm_num
  · convert tightQ0_156 using 1 <;> norm_num
  · convert tightQ0_157 using 1 <;> norm_num
  · convert tightQ0_158 using 1 <;> norm_num

theorem tightQ0_160 : TightBoxCovered (3 / 16) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_132 using 1 <;> norm_num
  · convert tightQ0_137 using 1 <;> norm_num
  · convert tightQ0_138 using 1 <;> norm_num
  · convert tightQ0_159 using 1 <;> norm_num

theorem tightQ0_161 : TightBoxCovered (7 / 32) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (1 / 4) (1 / 32) (742311 / 2000000) (312933 / 1000000) (304811 / 2000000) (62933 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_162 : TightBoxCovered (3 / 16) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (9 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (231319 / 2000000) (119129 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_163 : TightBoxCovered (7 / 32) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (9 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (304811 / 2000000) (31683 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_164 : TightBoxCovered (3 / 16) (1 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_160 using 1 <;> norm_num
  · convert tightQ0_161 using 1 <;> norm_num
  · convert tightQ0_162 using 1 <;> norm_num
  · convert tightQ0_163 using 1 <;> norm_num

theorem tightQ0_165 : TightBoxCovered (1 / 8) (5 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (5 / 16) (1 / 16) (206181 / 2000000) (400379 / 1000000) (168819 / 2000000) (87879 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_166 : TightBoxCovered (3 / 16) (5 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (5 / 16) (1 / 32) (206181 / 2000000) (400379 / 1000000) (231319 / 2000000) (87879 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_167 : TightBoxCovered (7 / 32) (5 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (5 / 16) (1 / 32) (742311 / 2000000) (312933 / 1000000) (304811 / 2000000) (30817 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_168 : TightBoxCovered (3 / 16) (11 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (11 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (231319 / 2000000) (56629 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_169 : TightBoxCovered (7 / 32) (11 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (11 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (293819 / 2000000) (56629 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_170 : TightBoxCovered (3 / 16) (5 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_166 using 1 <;> norm_num
  · convert tightQ0_167 using 1 <;> norm_num
  · convert tightQ0_168 using 1 <;> norm_num
  · convert tightQ0_169 using 1 <;> norm_num

theorem tightQ0_171 : TightBoxCovered (1 / 8) (1 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_131 using 1 <;> norm_num
  · convert tightQ0_164 using 1 <;> norm_num
  · convert tightQ0_165 using 1 <;> norm_num
  · convert tightQ0_170 using 1 <;> norm_num

theorem tightQ0_172 : TightBoxCovered 0 (3 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf 0 (3 / 8) (1 / 8) (206181 / 2000000) (400379 / 1000000) (206181 / 2000000) (99621 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_173 : TightBoxCovered (1 / 8) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (3 / 8) (1 / 16) (206181 / 2000000) (400379 / 1000000) (168819 / 2000000) (37121 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_174 : TightBoxCovered (3 / 16) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 16) (3 / 8) (1 / 16) (206181 / 2000000) (400379 / 1000000) (293819 / 2000000) (37121 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_175 : TightBoxCovered (1 / 8) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 8) (7 / 16) (1 / 16) (206181 / 2000000) (400379 / 1000000) (168819 / 2000000) (99621 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_176 : TightBoxCovered (3 / 16) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (7 / 16) (1 / 32) (206181 / 2000000) (400379 / 1000000) (231319 / 2000000) (68371 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_177 : TightBoxCovered (7 / 32) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 32) (7 / 16) (1 / 32) (206181 / 2000000) (400379 / 1000000) (293819 / 2000000) (68371 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_178 : TightBoxCovered (3 / 16) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 16) (15 / 32) (1 / 32) (206181 / 2000000) (400379 / 1000000) (231319 / 2000000) (99621 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_179 : TightBoxCovered (7 / 32) (15 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 32) (15 / 32) (1 / 64) (206181 / 2000000) (400379 / 1000000) (262569 / 2000000) (20999 / 250000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_180 : TightBoxCovered (15 / 64) (15 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 64) (15 / 32) (1 / 64) (206181 / 2000000) (400379 / 1000000) (293819 / 2000000) (20999 / 250000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_181 : TightBoxCovered (7 / 32) (31 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 32) (31 / 64) (1 / 64) (206181 / 2000000) (400379 / 1000000) (262569 / 2000000) (99621 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_182 : TightBoxCovered (15 / 64) (31 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 64) (31 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (2037 / 15625) (39841 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_183 : TightBoxCovered (7 / 32) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_179 using 1 <;> norm_num
  · convert tightQ0_180 using 1 <;> norm_num
  · convert tightQ0_181 using 1 <;> norm_num
  · convert tightQ0_182 using 1 <;> norm_num

theorem tightQ0_184 : TightBoxCovered (3 / 16) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_176 using 1 <;> norm_num
  · convert tightQ0_177 using 1 <;> norm_num
  · convert tightQ0_178 using 1 <;> norm_num
  · convert tightQ0_183 using 1 <;> norm_num

theorem tightQ0_185 : TightBoxCovered (1 / 8) (3 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_173 using 1 <;> norm_num
  · convert tightQ0_174 using 1 <;> norm_num
  · convert tightQ0_175 using 1 <;> norm_num
  · convert tightQ0_184 using 1 <;> norm_num

theorem tightQ0_186 : TightBoxCovered 0 (1 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ0_126 using 1 <;> norm_num
  · convert tightQ0_171 using 1 <;> norm_num
  · convert tightQ0_172 using 1 <;> norm_num
  · convert tightQ0_185 using 1 <;> norm_num

theorem tightQ0_187 : TightBoxCovered (1 / 4) (1 / 4) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 4) (1 / 4) (1 / 8) (742311 / 2000000) (312933 / 1000000) (242311 / 2000000) (62933 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_188 : TightBoxCovered (3 / 8) (1 / 4) (1 / 8) := by
  apply tightBoxCovered_leaf (3 / 8) (1 / 4) (1 / 8) (742311 / 2000000) (312933 / 1000000) (257689 / 2000000) (62933 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_189 : TightBoxCovered (1 / 4) (3 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 4) (3 / 8) (1 / 32) (742311 / 2000000) (312933 / 1000000) (242311 / 2000000) (93317 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_190 : TightBoxCovered (9 / 32) (3 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (3 / 8) (1 / 32) (742311 / 2000000) (312933 / 1000000) (179811 / 2000000) (93317 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_191 : TightBoxCovered (1 / 4) (13 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (13 / 32) (1 / 64) (206181 / 2000000) (400379 / 1000000) (325069 / 2000000) (2687 / 125000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_192 : TightBoxCovered (17 / 64) (13 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (13 / 32) (1 / 64) (742311 / 2000000) (312933 / 1000000) (211061 / 2000000) (54471 / 500000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_193 : TightBoxCovered (1 / 4) (27 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 4) (27 / 64) (1 / 64) (206181 / 2000000) (400379 / 1000000) (325069 / 2000000) (37121 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_194 : TightBoxCovered (17 / 64) (27 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (27 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (211061 / 2000000) (124567 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_195 : TightBoxCovered (1 / 4) (13 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_191 using 1 <;> norm_num
  · convert tightQ0_192 using 1 <;> norm_num
  · convert tightQ0_193 using 1 <;> norm_num
  · convert tightQ0_194 using 1 <;> norm_num

theorem tightQ0_196 : TightBoxCovered (9 / 32) (13 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (13 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (179811 / 2000000) (124567 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_197 : TightBoxCovered (1 / 4) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_189 using 1 <;> norm_num
  · convert tightQ0_190 using 1 <;> norm_num
  · convert tightQ0_195 using 1 <;> norm_num
  · convert tightQ0_196 using 1 <;> norm_num

theorem tightQ0_198 : TightBoxCovered (5 / 16) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 16) (3 / 8) (1 / 16) (742311 / 2000000) (312933 / 1000000) (117311 / 2000000) (124567 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_199 : TightBoxCovered (1 / 4) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (7 / 16) (1 / 128) (206181 / 2000000) (400379 / 1000000) (77361 / 500000) (89867 / 2000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_200 : TightBoxCovered (33 / 128) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (7 / 16) (1 / 128) (206181 / 2000000) (400379 / 1000000) (325069 / 2000000) (89867 / 2000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_201 : TightBoxCovered (1 / 4) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (57 / 128) (1 / 128) (206181 / 2000000) (400379 / 1000000) (77361 / 500000) (26373 / 500000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_202 : TightBoxCovered (33 / 128) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (33 / 128) (57 / 128) (1 / 256) (206181 / 2000000) (400379 / 1000000) (634513 / 4000000) (195359 / 4000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_203 : TightBoxCovered (67 / 256) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 256) (57 / 128) (1 / 256) (206181 / 2000000) (400379 / 1000000) (325069 / 2000000) (195359 / 4000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_204 : TightBoxCovered (33 / 128) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (33 / 128) (115 / 256) (1 / 256) (206181 / 2000000) (400379 / 1000000) (634513 / 4000000) (26373 / 500000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_205 : TightBoxCovered (67 / 256) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (67 / 256) (115 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (412097 / 4000000) (107807 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_206 : TightBoxCovered (33 / 128) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ0_202 using 1 <;> norm_num
  · convert tightQ0_203 using 1 <;> norm_num
  · convert tightQ0_204 using 1 <;> norm_num
  · convert tightQ0_205 using 1 <;> norm_num

theorem tightQ0_207 : TightBoxCovered (1 / 4) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_199 using 1 <;> norm_num
  · convert tightQ0_200 using 1 <;> norm_num
  · convert tightQ0_201 using 1 <;> norm_num
  · convert tightQ0_206 using 1 <;> norm_num

theorem tightQ0_208 : TightBoxCovered (17 / 64) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 64) (7 / 16) (1 / 128) (742311 / 2000000) (312933 / 1000000) (211061 / 2000000) (264759 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_209 : TightBoxCovered (35 / 128) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (7 / 16) (1 / 128) (742311 / 2000000) (312933 / 1000000) (48859 / 500000) (264759 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_210 : TightBoxCovered (17 / 64) (57 / 128) (1 / 1024) := by
  apply tightBoxCovered_leaf (17 / 64) (57 / 128) (1 / 1024) (206181 / 2000000) (400379 / 1000000) (2616177 / 16000000) (734561 / 16000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_211 : TightBoxCovered (273 / 1024) (57 / 128) (1 / 1024) := by
  apply tightBoxCovered_leaf (273 / 1024) (57 / 128) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (1672863 / 16000000) (2133697 / 16000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_212 : TightBoxCovered (17 / 64) (457 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (17 / 64) (457 / 1024) (1 / 1024) (364743 / 1000000) (233591 / 400000) (49559 / 500000) (440603 / 3200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_213 : TightBoxCovered (273 / 1024) (457 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (273 / 1024) (457 / 1024) (1 / 1024) (364743 / 1000000) (233591 / 400000) (1570263 / 16000000) (440603 / 3200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_214 : TightBoxCovered (17 / 64) (57 / 128) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ0_210 using 1 <;> norm_num
  · convert tightQ0_211 using 1 <;> norm_num
  · convert tightQ0_212 using 1 <;> norm_num
  · convert tightQ0_213 using 1 <;> norm_num

theorem tightQ0_215 : TightBoxCovered (137 / 512) (57 / 128) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 512) (57 / 128) (1 / 512) (742311 / 2000000) (312933 / 1000000) (828619 / 8000000) (1074661 / 8000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_216 : TightBoxCovered (17 / 64) (229 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (17 / 64) (229 / 512) (1 / 512) (364743 / 1000000) (233591 / 400000) (49559 / 500000) (218739 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_217 : TightBoxCovered (137 / 512) (229 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 512) (229 / 512) (1 / 512) (364743 / 1000000) (233591 / 400000) (777319 / 8000000) (218739 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_218 : TightBoxCovered (17 / 64) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ0_214 using 1 <;> norm_num
  · convert tightQ0_215 using 1 <;> norm_num
  · convert tightQ0_216 using 1 <;> norm_num
  · convert tightQ0_217 using 1 <;> norm_num

theorem tightQ0_219 : TightBoxCovered (69 / 256) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (57 / 128) (1 / 256) (364743 / 1000000) (233591 / 400000) (380847 / 4000000) (27733 / 200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_220 : TightBoxCovered (17 / 64) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 64) (115 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (49559 / 500000) (107807 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_221 : TightBoxCovered (69 / 256) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 256) (115 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (380847 / 4000000) (107807 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_222 : TightBoxCovered (17 / 64) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ0_218 using 1 <;> norm_num
  · convert tightQ0_219 using 1 <;> norm_num
  · convert tightQ0_220 using 1 <;> norm_num
  · convert tightQ0_221 using 1 <;> norm_num

theorem tightQ0_223 : TightBoxCovered (35 / 128) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (35 / 128) (57 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (182611 / 2000000) (27733 / 200000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_224 : TightBoxCovered (17 / 64) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_208 using 1 <;> norm_num
  · convert tightQ0_209 using 1 <;> norm_num
  · convert tightQ0_222 using 1 <;> norm_num
  · convert tightQ0_223 using 1 <;> norm_num

theorem tightQ0_225 : TightBoxCovered (1 / 4) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (29 / 64) (1 / 128) (206181 / 2000000) (400379 / 1000000) (77361 / 500000) (121117 / 2000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_226 : TightBoxCovered (33 / 128) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (29 / 64) (1 / 128) (364743 / 1000000) (233591 / 400000) (213861 / 2000000) (52341 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_227 : TightBoxCovered (1 / 4) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (1 / 4) (59 / 128) (1 / 128) (206181 / 2000000) (400379 / 1000000) (77361 / 500000) (68371 / 1000000) ⟨4, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_228 : TightBoxCovered (33 / 128) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 128) (59 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (213861 / 2000000) (769 / 6250) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_229 : TightBoxCovered (1 / 4) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_225 using 1 <;> norm_num
  · convert tightQ0_226 using 1 <;> norm_num
  · convert tightQ0_227 using 1 <;> norm_num
  · convert tightQ0_228 using 1 <;> norm_num

theorem tightQ0_230 : TightBoxCovered (17 / 64) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 64) (29 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (49559 / 500000) (52341 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_231 : TightBoxCovered (1 / 4) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_207 using 1 <;> norm_num
  · convert tightQ0_224 using 1 <;> norm_num
  · convert tightQ0_229 using 1 <;> norm_num
  · convert tightQ0_230 using 1 <;> norm_num

theorem tightQ0_232 : TightBoxCovered (9 / 32) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (7 / 16) (1 / 32) (364743 / 1000000) (233591 / 400000) (83493 / 1000000) (58591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_233 : TightBoxCovered (1 / 4) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 4) (15 / 32) (1 / 32) (364743 / 1000000) (233591 / 400000) (114743 / 1000000) (46091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_234 : TightBoxCovered (9 / 32) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 32) (15 / 32) (1 / 32) (364743 / 1000000) (233591 / 400000) (83493 / 1000000) (46091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_235 : TightBoxCovered (1 / 4) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_231 using 1 <;> norm_num
  · convert tightQ0_232 using 1 <;> norm_num
  · convert tightQ0_233 using 1 <;> norm_num
  · convert tightQ0_234 using 1 <;> norm_num

theorem tightQ0_236 : TightBoxCovered (5 / 16) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 16) (7 / 16) (1 / 16) (364743 / 1000000) (233591 / 400000) (52243 / 1000000) (58591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_237 : TightBoxCovered (1 / 4) (3 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_197 using 1 <;> norm_num
  · convert tightQ0_198 using 1 <;> norm_num
  · convert tightQ0_235 using 1 <;> norm_num
  · convert tightQ0_236 using 1 <;> norm_num

theorem tightQ0_238 : TightBoxCovered (3 / 8) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (3 / 8) (1 / 16) (742311 / 2000000) (312933 / 1000000) (132689 / 2000000) (124567 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_239 : TightBoxCovered (7 / 16) (3 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (3 / 8) (1 / 32) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (93317 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_240 : TightBoxCovered (15 / 32) (3 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (3 / 8) (1 / 32) (742311 / 2000000) (312933 / 1000000) (257689 / 2000000) (93317 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_241 : TightBoxCovered (7 / 16) (13 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (13 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (124567 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_242 : TightBoxCovered (15 / 32) (13 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 32) (13 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (166507 / 1000000) (8591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_243 : TightBoxCovered (7 / 16) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_239 using 1 <;> norm_num
  · convert tightQ0_240 using 1 <;> norm_num
  · convert tightQ0_241 using 1 <;> norm_num
  · convert tightQ0_242 using 1 <;> norm_num

theorem tightQ0_244 : TightBoxCovered (3 / 8) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 8) (7 / 16) (1 / 16) (364743 / 1000000) (233591 / 400000) (72757 / 1000000) (58591 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_245 : TightBoxCovered (7 / 16) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (7 / 16) (1 / 64) (742311 / 2000000) (312933 / 1000000) (163939 / 2000000) (4381 / 31250) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_246 : TightBoxCovered (29 / 64) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (7 / 16) (1 / 128) (742311 / 2000000) (312933 / 1000000) (44891 / 500000) (264759 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_247 : TightBoxCovered (59 / 128) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (59 / 128) (7 / 16) (1 / 128) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (264759 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_248 : TightBoxCovered (29 / 64) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (29 / 64) (57 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (44891 / 500000) (4381 / 31250) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_249 : TightBoxCovered (59 / 128) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (59 / 128) (57 / 128) (1 / 256) (742311 / 2000000) (312933 / 1000000) (374753 / 4000000) (545143 / 4000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_250 : TightBoxCovered (119 / 256) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (119 / 256) (57 / 128) (1 / 256) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (545143 / 4000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_251 : TightBoxCovered (59 / 128) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (59 / 128) (115 / 256) (1 / 256) (742311 / 2000000) (312933 / 1000000) (374753 / 4000000) (4381 / 31250) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_252 : TightBoxCovered (119 / 256) (115 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (119 / 256) (115 / 256) (1 / 512) (742311 / 2000000) (312933 / 1000000) (765131 / 8000000) (1105911 / 8000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_253 : TightBoxCovered (239 / 512) (115 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (239 / 512) (115 / 256) (1 / 512) (742311 / 2000000) (312933 / 1000000) (195189 / 2000000) (1105911 / 8000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_254 : TightBoxCovered (119 / 256) (231 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (119 / 256) (231 / 512) (1 / 512) (742311 / 2000000) (312933 / 1000000) (765131 / 8000000) (4381 / 31250) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_255 : TightBoxCovered (239 / 512) (231 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (239 / 512) (231 / 512) (1 / 512) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (212489 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_256 : TightBoxCovered (119 / 256) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ0_252 using 1 <;> norm_num
  · convert tightQ0_253 using 1 <;> norm_num
  · convert tightQ0_254 using 1 <;> norm_num
  · convert tightQ0_255 using 1 <;> norm_num

theorem tightQ0_257 : TightBoxCovered (59 / 128) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ0_249 using 1 <;> norm_num
  · convert tightQ0_250 using 1 <;> norm_num
  · convert tightQ0_251 using 1 <;> norm_num
  · convert tightQ0_256 using 1 <;> norm_num

theorem tightQ0_258 : TightBoxCovered (29 / 64) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_246 using 1 <;> norm_num
  · convert tightQ0_247 using 1 <;> norm_num
  · convert tightQ0_248 using 1 <;> norm_num
  · convert tightQ0_257 using 1 <;> norm_num

theorem tightQ0_259 : TightBoxCovered (7 / 16) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (7 / 16) (29 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (44191 / 500000) (52341 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_260 : TightBoxCovered (29 / 64) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (29 / 64) (29 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (52341 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_261 : TightBoxCovered (7 / 16) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_245 using 1 <;> norm_num
  · convert tightQ0_258 using 1 <;> norm_num
  · convert tightQ0_259 using 1 <;> norm_num
  · convert tightQ0_260 using 1 <;> norm_num

theorem tightQ0_262 : TightBoxCovered (15 / 32) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 32) (7 / 16) (1 / 128) (742311 / 2000000) (312933 / 1000000) (105407 / 1000000) (264759 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_263 : TightBoxCovered (61 / 128) (7 / 16) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (7 / 16) (1 / 128) (635257 / 1000000) (166409 / 400000) (317389 / 2000000) (2929 / 100000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_264 : TightBoxCovered (15 / 32) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (15 / 32) (57 / 128) (1 / 256) (742311 / 2000000) (312933 / 1000000) (406003 / 4000000) (545143 / 4000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_265 : TightBoxCovered (121 / 256) (57 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (121 / 256) (57 / 128) (1 / 256) (635257 / 1000000) (166409 / 400000) (650403 / 4000000) (26557 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_266 : TightBoxCovered (15 / 32) (115 / 256) (1 / 1024) := by
  apply tightBoxCovered_leaf (15 / 32) (115 / 256) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (1577137 / 16000000) (2196197 / 16000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_267 : TightBoxCovered (481 / 1024) (115 / 256) (1 / 1024) := by
  apply tightBoxCovered_leaf (481 / 1024) (115 / 256) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (796381 / 8000000) (2196197 / 16000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_268 : TightBoxCovered (15 / 32) (461 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (15 / 32) (461 / 1024) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (1577137 / 16000000) (1105911 / 8000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_269 : TightBoxCovered (481 / 1024) (461 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (481 / 1024) (461 / 1024) (1 / 1024) (635257 / 1000000) (166409 / 400000) (2648487 / 16000000) (56239 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_270 : TightBoxCovered (15 / 32) (115 / 256) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ0_266 using 1 <;> norm_num
  · convert tightQ0_267 using 1 <;> norm_num
  · convert tightQ0_268 using 1 <;> norm_num
  · convert tightQ0_269 using 1 <;> norm_num

theorem tightQ0_271 : TightBoxCovered (241 / 512) (115 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (241 / 512) (115 / 256) (1 / 512) (635257 / 1000000) (166409 / 400000) (1316431 / 8000000) (56239 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_272 : TightBoxCovered (15 / 32) (231 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (15 / 32) (231 / 512) (1 / 512) (364743 / 1000000) (233591 / 400000) (847681 / 8000000) (212489 / 1600000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_273 : TightBoxCovered (241 / 512) (231 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (241 / 512) (231 / 512) (1 / 512) (635257 / 1000000) (166409 / 400000) (1316431 / 8000000) (14841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_274 : TightBoxCovered (15 / 32) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ0_270 using 1 <;> norm_num
  · convert tightQ0_271 using 1 <;> norm_num
  · convert tightQ0_272 using 1 <;> norm_num
  · convert tightQ0_273 using 1 <;> norm_num

theorem tightQ0_275 : TightBoxCovered (121 / 256) (115 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (121 / 256) (115 / 256) (1 / 256) (635257 / 1000000) (166409 / 400000) (650403 / 4000000) (14841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_276 : TightBoxCovered (15 / 32) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ0_264 using 1 <;> norm_num
  · convert tightQ0_265 using 1 <;> norm_num
  · convert tightQ0_274 using 1 <;> norm_num
  · convert tightQ0_275 using 1 <;> norm_num

theorem tightQ0_277 : TightBoxCovered (61 / 128) (57 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (57 / 128) (1 / 128) (635257 / 1000000) (166409 / 400000) (317389 / 2000000) (14841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_278 : TightBoxCovered (15 / 32) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_262 using 1 <;> norm_num
  · convert tightQ0_263 using 1 <;> norm_num
  · convert tightQ0_276 using 1 <;> norm_num
  · convert tightQ0_277 using 1 <;> norm_num

theorem tightQ0_279 : TightBoxCovered (31 / 64) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (7 / 16) (1 / 64) (635257 / 1000000) (166409 / 400000) (75441 / 500000) (14841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_280 : TightBoxCovered (15 / 32) (29 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (15 / 32) (29 / 64) (1 / 256) (364743 / 1000000) (233591 / 400000) (431653 / 4000000) (52341 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_281 : TightBoxCovered (121 / 256) (29 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (121 / 256) (29 / 64) (1 / 256) (635257 / 1000000) (166409 / 400000) (650403 / 4000000) (32807 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_282 : TightBoxCovered (15 / 32) (117 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (15 / 32) (117 / 256) (1 / 256) (364743 / 1000000) (233591 / 400000) (431653 / 4000000) (101557 / 800000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_283 : TightBoxCovered (121 / 256) (117 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (121 / 256) (117 / 256) (1 / 256) (635257 / 1000000) (166409 / 400000) (650403 / 4000000) (8983 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_284 : TightBoxCovered (15 / 32) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ0_280 using 1 <;> norm_num
  · convert tightQ0_281 using 1 <;> norm_num
  · convert tightQ0_282 using 1 <;> norm_num
  · convert tightQ0_283 using 1 <;> norm_num

theorem tightQ0_285 : TightBoxCovered (61 / 128) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (29 / 64) (1 / 128) (635257 / 1000000) (166409 / 400000) (317389 / 2000000) (8983 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_286 : TightBoxCovered (15 / 32) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (15 / 32) (59 / 128) (1 / 128) (364743 / 1000000) (233591 / 400000) (223639 / 2000000) (769 / 6250) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_287 : TightBoxCovered (61 / 128) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (61 / 128) (59 / 128) (1 / 128) (635257 / 1000000) (166409 / 400000) (317389 / 2000000) (21091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_288 : TightBoxCovered (15 / 32) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ0_284 using 1 <;> norm_num
  · convert tightQ0_285 using 1 <;> norm_num
  · convert tightQ0_286 using 1 <;> norm_num
  · convert tightQ0_287 using 1 <;> norm_num

theorem tightQ0_289 : TightBoxCovered (31 / 64) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (29 / 64) (1 / 64) (635257 / 1000000) (166409 / 400000) (75441 / 500000) (21091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_290 : TightBoxCovered (15 / 32) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_278 using 1 <;> norm_num
  · convert tightQ0_279 using 1 <;> norm_num
  · convert tightQ0_288 using 1 <;> norm_num
  · convert tightQ0_289 using 1 <;> norm_num

theorem tightQ0_291 : TightBoxCovered (7 / 16) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (7 / 16) (15 / 32) (1 / 32) (364743 / 1000000) (233591 / 400000) (104007 / 1000000) (46091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_292 : TightBoxCovered (15 / 32) (15 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (15 / 32) (1 / 64) (364743 / 1000000) (233591 / 400000) (7477 / 62500) (46091 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_293 : TightBoxCovered (31 / 64) (15 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (15 / 32) (1 / 64) (635257 / 1000000) (166409 / 400000) (75441 / 500000) (27341 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_294 : TightBoxCovered (15 / 32) (31 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (15 / 32) (31 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (7477 / 62500) (39841 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_295 : TightBoxCovered (31 / 64) (31 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 64) (31 / 64) (1 / 64) (364743 / 1000000) (233591 / 400000) (135257 / 1000000) (39841 / 400000) ⟨9, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ0_296 : TightBoxCovered (15 / 32) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ0_292 using 1 <;> norm_num
  · convert tightQ0_293 using 1 <;> norm_num
  · convert tightQ0_294 using 1 <;> norm_num
  · convert tightQ0_295 using 1 <;> norm_num

theorem tightQ0_297 : TightBoxCovered (7 / 16) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ0_261 using 1 <;> norm_num
  · convert tightQ0_290 using 1 <;> norm_num
  · convert tightQ0_291 using 1 <;> norm_num
  · convert tightQ0_296 using 1 <;> norm_num

theorem tightQ0_298 : TightBoxCovered (3 / 8) (3 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ0_238 using 1 <;> norm_num
  · convert tightQ0_243 using 1 <;> norm_num
  · convert tightQ0_244 using 1 <;> norm_num
  · convert tightQ0_297 using 1 <;> norm_num

theorem tightQ0_299 : TightBoxCovered (1 / 4) (1 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ0_187 using 1 <;> norm_num
  · convert tightQ0_188 using 1 <;> norm_num
  · convert tightQ0_237 using 1 <;> norm_num
  · convert tightQ0_298 using 1 <;> norm_num

theorem tightQ0_300 : TightBoxCovered 0 0 (1 / 2) := by
  apply tightBoxCovered_split
  · convert tightQ0_36 using 1 <;> norm_num
  · convert tightQ0_113 using 1 <;> norm_num
  · convert tightQ0_186 using 1 <;> norm_num
  · convert tightQ0_299 using 1 <;> norm_num

theorem tightQuadrant0 : TightBoxCovered 0 0 (1/2) := tightQ0_300

end ElevenSquare
