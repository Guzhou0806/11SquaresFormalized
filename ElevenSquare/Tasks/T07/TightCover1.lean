import ElevenSquare.Tasks.T07.TightCoverChecks

/-! Untrusted generated dyadic tree, checked by Lean at every leaf. -/
namespace ElevenSquare
set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

theorem tightQ1_0 : TightBoxCovered (1 / 2) 0 (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) 0 (1 / 32) (186601 / 500000) (45503 / 1000000) (4939 / 31250) (45503 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_1 : TightBoxCovered (17 / 32) 0 (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 32) 0 (1 / 256) (186601 / 500000) (45503 / 1000000) (647817 / 4000000) (45503 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_2 : TightBoxCovered (137 / 256) 0 (1 / 1024) := by
  apply tightBoxCovered_leaf (137 / 256) 0 (1 / 1024) (186601 / 500000) (45503 / 1000000) (2606893 / 16000000) (45503 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_3 : TightBoxCovered (549 / 1024) 0 (1 / 1024) := by
  apply tightBoxCovered_leaf (549 / 1024) 0 (1 / 1024) (1267243 / 2000000) (34689 / 250000) (1559819 / 16000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_4 : TightBoxCovered (137 / 256) (1 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (137 / 256) (1 / 1024) (1 / 1024) (186601 / 500000) (45503 / 1000000) (2606893 / 16000000) (712423 / 16000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_5 : TightBoxCovered (549 / 1024) (1 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (549 / 1024) (1 / 1024) (1 / 1024) (186601 / 500000) (45503 / 1000000) (1311259 / 8000000) (712423 / 16000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_6 : TightBoxCovered (137 / 256) 0 (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ1_2 using 1 <;> norm_num
  · convert tightQ1_3 using 1 <;> norm_num
  · convert tightQ1_4 using 1 <;> norm_num
  · convert tightQ1_5 using 1 <;> norm_num

theorem tightQ1_7 : TightBoxCovered (275 / 512) 0 (1 / 512) := by
  apply tightBoxCovered_leaf (275 / 512) 0 (1 / 512) (1267243 / 2000000) (34689 / 250000) (772097 / 8000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_8 : TightBoxCovered (137 / 256) (1 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 256) (1 / 512) (1 / 512) (186601 / 500000) (45503 / 1000000) (1311259 / 8000000) (348399 / 8000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_9 : TightBoxCovered (275 / 512) (1 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (275 / 512) (1 / 512) (1 / 512) (1267243 / 2000000) (34689 / 250000) (772097 / 8000000) (1094423 / 8000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_10 : TightBoxCovered (137 / 256) 0 (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ1_6 using 1 <;> norm_num
  · convert tightQ1_7 using 1 <;> norm_num
  · convert tightQ1_8 using 1 <;> norm_num
  · convert tightQ1_9 using 1 <;> norm_num

theorem tightQ1_11 : TightBoxCovered (17 / 32) (1 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 32) (1 / 256) (1 / 256) (186601 / 500000) (45503 / 1000000) (647817 / 4000000) (166387 / 4000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_12 : TightBoxCovered (137 / 256) (1 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (137 / 256) (1 / 256) (1 / 256) (1267243 / 2000000) (34689 / 250000) (393861 / 4000000) (539399 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_13 : TightBoxCovered (17 / 32) 0 (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_1 using 1 <;> norm_num
  · convert tightQ1_10 using 1 <;> norm_num
  · convert tightQ1_11 using 1 <;> norm_num
  · convert tightQ1_12 using 1 <;> norm_num

theorem tightQ1_14 : TightBoxCovered (69 / 128) 0 (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) 0 (1 / 128) (1267243 / 2000000) (34689 / 250000) (94559 / 1000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_15 : TightBoxCovered (17 / 32) (1 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 32) (1 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (204743 / 2000000) (261887 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_16 : TightBoxCovered (69 / 128) (1 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (1 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (94559 / 1000000) (261887 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_17 : TightBoxCovered (17 / 32) 0 (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_13 using 1 <;> norm_num
  · convert tightQ1_14 using 1 <;> norm_num
  · convert tightQ1_15 using 1 <;> norm_num
  · convert tightQ1_16 using 1 <;> norm_num

theorem tightQ1_18 : TightBoxCovered (35 / 64) 0 (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) 0 (1 / 64) (1267243 / 2000000) (34689 / 250000) (173493 / 2000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_19 : TightBoxCovered (17 / 32) (1 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 32) (1 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (204743 / 2000000) (123131 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_20 : TightBoxCovered (35 / 64) (1 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (1 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (173493 / 2000000) (123131 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_21 : TightBoxCovered (17 / 32) 0 (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_17 using 1 <;> norm_num
  · convert tightQ1_18 using 1 <;> norm_num
  · convert tightQ1_19 using 1 <;> norm_num
  · convert tightQ1_20 using 1 <;> norm_num

theorem tightQ1_22 : TightBoxCovered (1 / 2) (1 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (1 / 32) (1 / 32) (186601 / 500000) (45503 / 1000000) (4939 / 31250) (16997 / 1000000) ⟨1, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_23 : TightBoxCovered (17 / 32) (1 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (1 / 32) (1 / 32) (1267243 / 2000000) (34689 / 250000) (204743 / 2000000) (53753 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_24 : TightBoxCovered (1 / 2) 0 (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_0 using 1 <;> norm_num
  · convert tightQ1_21 using 1 <;> norm_num
  · convert tightQ1_22 using 1 <;> norm_num
  · convert tightQ1_23 using 1 <;> norm_num

theorem tightQ1_25 : TightBoxCovered (9 / 16) 0 (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) 0 (1 / 16) (1267243 / 2000000) (34689 / 250000) (142243 / 2000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_26 : TightBoxCovered (1 / 2) (1 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 2) (1 / 16) (1 / 16) (1267243 / 2000000) (34689 / 250000) (267243 / 2000000) (2383 / 31250) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_27 : TightBoxCovered (9 / 16) (1 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (1 / 16) (1 / 16) (1267243 / 2000000) (34689 / 250000) (142243 / 2000000) (2383 / 31250) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_28 : TightBoxCovered (1 / 2) 0 (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_24 using 1 <;> norm_num
  · convert tightQ1_25 using 1 <;> norm_num
  · convert tightQ1_26 using 1 <;> norm_num
  · convert tightQ1_27 using 1 <;> norm_num

theorem tightQ1_29 : TightBoxCovered (5 / 8) 0 (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 8) 0 (1 / 16) (1267243 / 2000000) (34689 / 250000) (107757 / 2000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_30 : TightBoxCovered (11 / 16) 0 (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) 0 (1 / 32) (1267243 / 2000000) (34689 / 250000) (170257 / 2000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_31 : TightBoxCovered (23 / 32) 0 (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) 0 (1 / 128) (1267243 / 2000000) (34689 / 250000) (92941 / 1000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_32 : TightBoxCovered (93 / 128) 0 (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) 0 (1 / 256) (1267243 / 2000000) (34689 / 250000) (387389 / 4000000) (34689 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_33 : TightBoxCovered (187 / 256) 0 (1 / 256) := by
  apply tightBoxCovered_leaf (187 / 256) 0 (1 / 256) (1731123 / 2000000) (25701 / 250000) (540371 / 4000000) (25701 / 250000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_34 : TightBoxCovered (93 / 128) (1 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) (1 / 256) (1 / 256) (1267243 / 2000000) (34689 / 250000) (387389 / 4000000) (539399 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_35 : TightBoxCovered (187 / 256) (1 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (187 / 256) (1 / 256) (1 / 256) (1267243 / 2000000) (34689 / 250000) (201507 / 2000000) (539399 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_36 : TightBoxCovered (93 / 128) 0 (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_32 using 1 <;> norm_num
  · convert tightQ1_33 using 1 <;> norm_num
  · convert tightQ1_34 using 1 <;> norm_num
  · convert tightQ1_35 using 1 <;> norm_num

theorem tightQ1_37 : TightBoxCovered (23 / 32) (1 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) (1 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (92941 / 1000000) (261887 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_38 : TightBoxCovered (93 / 128) (1 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (93 / 128) (1 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (201507 / 2000000) (261887 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_39 : TightBoxCovered (23 / 32) 0 (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_31 using 1 <;> norm_num
  · convert tightQ1_36 using 1 <;> norm_num
  · convert tightQ1_37 using 1 <;> norm_num
  · convert tightQ1_38 using 1 <;> norm_num

theorem tightQ1_40 : TightBoxCovered (47 / 64) 0 (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) 0 (1 / 64) (1731123 / 2000000) (25701 / 250000) (262373 / 2000000) (25701 / 250000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_41 : TightBoxCovered (23 / 32) (1 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (1 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (201507 / 2000000) (123131 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_42 : TightBoxCovered (47 / 64) (1 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (1 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (232757 / 2000000) (123131 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_43 : TightBoxCovered (23 / 32) 0 (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_39 using 1 <;> norm_num
  · convert tightQ1_40 using 1 <;> norm_num
  · convert tightQ1_41 using 1 <;> norm_num
  · convert tightQ1_42 using 1 <;> norm_num

theorem tightQ1_44 : TightBoxCovered (11 / 16) (1 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (1 / 32) (1 / 32) (1267243 / 2000000) (34689 / 250000) (170257 / 2000000) (53753 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_45 : TightBoxCovered (23 / 32) (1 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (23 / 32) (1 / 32) (1 / 32) (1267243 / 2000000) (34689 / 250000) (232757 / 2000000) (53753 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_46 : TightBoxCovered (11 / 16) 0 (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_30 using 1 <;> norm_num
  · convert tightQ1_43 using 1 <;> norm_num
  · convert tightQ1_44 using 1 <;> norm_num
  · convert tightQ1_45 using 1 <;> norm_num

theorem tightQ1_47 : TightBoxCovered (5 / 8) (1 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 8) (1 / 16) (1 / 16) (1267243 / 2000000) (34689 / 250000) (107757 / 2000000) (2383 / 31250) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_48 : TightBoxCovered (11 / 16) (1 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (11 / 16) (1 / 16) (1 / 16) (1267243 / 2000000) (34689 / 250000) (232757 / 2000000) (2383 / 31250) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_49 : TightBoxCovered (5 / 8) 0 (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_29 using 1 <;> norm_num
  · convert tightQ1_46 using 1 <;> norm_num
  · convert tightQ1_47 using 1 <;> norm_num
  · convert tightQ1_48 using 1 <;> norm_num

theorem tightQ1_50 : TightBoxCovered (1 / 2) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (1 / 2) (1 / 8) (1 / 16) (1267243 / 2000000) (34689 / 250000) (267243 / 2000000) (6093 / 125000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_51 : TightBoxCovered (9 / 16) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (1 / 8) (1 / 16) (1267243 / 2000000) (34689 / 250000) (142243 / 2000000) (6093 / 125000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_52 : TightBoxCovered (1 / 2) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (3 / 16) (1 / 32) (1267243 / 2000000) (34689 / 250000) (267243 / 2000000) (39997 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_53 : TightBoxCovered (17 / 32) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (3 / 16) (1 / 32) (1267243 / 2000000) (34689 / 250000) (204743 / 2000000) (39997 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_54 : TightBoxCovered (1 / 2) (7 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (7 / 32) (1 / 64) (1267243 / 2000000) (34689 / 250000) (267243 / 2000000) (95619 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_55 : TightBoxCovered (33 / 64) (7 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (7 / 32) (1 / 64) (1267243 / 2000000) (34689 / 250000) (235993 / 2000000) (95619 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_56 : TightBoxCovered (1 / 2) (15 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (15 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (288939 / 2000000) (39279 / 500000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_57 : TightBoxCovered (33 / 64) (15 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (15 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (235993 / 2000000) (27811 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_58 : TightBoxCovered (1 / 2) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_54 using 1 <;> norm_num
  · convert tightQ1_55 using 1 <;> norm_num
  · convert tightQ1_56 using 1 <;> norm_num
  · convert tightQ1_57 using 1 <;> norm_num

theorem tightQ1_59 : TightBoxCovered (17 / 32) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (7 / 32) (1 / 32) (1267243 / 2000000) (34689 / 250000) (204743 / 2000000) (27811 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_60 : TightBoxCovered (1 / 2) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_52 using 1 <;> norm_num
  · convert tightQ1_53 using 1 <;> norm_num
  · convert tightQ1_58 using 1 <;> norm_num
  · convert tightQ1_59 using 1 <;> norm_num

theorem tightQ1_61 : TightBoxCovered (9 / 16) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (3 / 16) (1 / 16) (1267243 / 2000000) (34689 / 250000) (142243 / 2000000) (27811 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_62 : TightBoxCovered (1 / 2) (1 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_50 using 1 <;> norm_num
  · convert tightQ1_51 using 1 <;> norm_num
  · convert tightQ1_60 using 1 <;> norm_num
  · convert tightQ1_61 using 1 <;> norm_num

theorem tightQ1_63 : TightBoxCovered (5 / 8) (1 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (5 / 8) (1 / 8) (1 / 8) (1267243 / 2000000) (34689 / 250000) (232757 / 2000000) (27811 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_64 : TightBoxCovered (1 / 2) 0 (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ1_28 using 1 <;> norm_num
  · convert tightQ1_49 using 1 <;> norm_num
  · convert tightQ1_62 using 1 <;> norm_num
  · convert tightQ1_63 using 1 <;> norm_num

theorem tightQ1_65 : TightBoxCovered (3 / 4) 0 (1 / 8) := by
  apply tightBoxCovered_leaf (3 / 4) 0 (1 / 8) (1731123 / 2000000) (25701 / 250000) (231123 / 2000000) (25701 / 250000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_66 : TightBoxCovered (7 / 8) 0 (1 / 8) := by
  apply tightBoxCovered_leaf (7 / 8) 0 (1 / 8) (1731123 / 2000000) (25701 / 250000) (268877 / 2000000) (25701 / 250000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_67 : TightBoxCovered (3 / 4) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (3 / 4) (1 / 8) (1 / 16) (1731123 / 2000000) (25701 / 250000) (231123 / 2000000) (10587 / 125000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_68 : TightBoxCovered (13 / 16) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (1 / 8) (1 / 16) (1731123 / 2000000) (25701 / 250000) (106123 / 2000000) (10587 / 125000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_69 : TightBoxCovered (3 / 4) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (3 / 16) (1 / 32) (1267243 / 2000000) (34689 / 250000) (295257 / 2000000) (39997 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_70 : TightBoxCovered (25 / 32) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (3 / 16) (1 / 32) (1731123 / 2000000) (25701 / 250000) (168623 / 2000000) (57973 / 500000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_71 : TightBoxCovered (3 / 4) (7 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (3 / 4) (7 / 32) (1 / 64) (1267243 / 2000000) (34689 / 250000) (264007 / 2000000) (95619 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_72 : TightBoxCovered (49 / 64) (7 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (49 / 64) (7 / 32) (1 / 64) (1731123 / 2000000) (25701 / 250000) (199873 / 2000000) (131571 / 1000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_73 : TightBoxCovered (3 / 4) (15 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (3 / 4) (15 / 64) (1 / 128) (1267243 / 2000000) (34689 / 250000) (124191 / 1000000) (206863 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_74 : TightBoxCovered (97 / 128) (15 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (97 / 128) (15 / 64) (1 / 128) (1267243 / 2000000) (34689 / 250000) (264007 / 2000000) (206863 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_75 : TightBoxCovered (3 / 4) (31 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (3 / 4) (31 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (124191 / 1000000) (27811 / 250000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_76 : TightBoxCovered (97 / 128) (31 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (97 / 128) (31 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (266131 / 2000000) (186677 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_77 : TightBoxCovered (3 / 4) (15 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_73 using 1 <;> norm_num
  · convert tightQ1_74 using 1 <;> norm_num
  · convert tightQ1_75 using 1 <;> norm_num
  · convert tightQ1_76 using 1 <;> norm_num

theorem tightQ1_78 : TightBoxCovered (49 / 64) (15 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (49 / 64) (15 / 64) (1 / 64) (445439 / 500000) (167763 / 500000) (125253 / 1000000) (101151 / 1000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_79 : TightBoxCovered (3 / 4) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_71 using 1 <;> norm_num
  · convert tightQ1_72 using 1 <;> norm_num
  · convert tightQ1_77 using 1 <;> norm_num
  · convert tightQ1_78 using 1 <;> norm_num

theorem tightQ1_80 : TightBoxCovered (25 / 32) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (7 / 32) (1 / 32) (1731123 / 2000000) (25701 / 250000) (168623 / 2000000) (36799 / 250000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_81 : TightBoxCovered (3 / 4) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_69 using 1 <;> norm_num
  · convert tightQ1_70 using 1 <;> norm_num
  · convert tightQ1_79 using 1 <;> norm_num
  · convert tightQ1_80 using 1 <;> norm_num

theorem tightQ1_82 : TightBoxCovered (13 / 16) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (3 / 16) (1 / 16) (1731123 / 2000000) (25701 / 250000) (106123 / 2000000) (36799 / 250000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_83 : TightBoxCovered (3 / 4) (1 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_67 using 1 <;> norm_num
  · convert tightQ1_68 using 1 <;> norm_num
  · convert tightQ1_81 using 1 <;> norm_num
  · convert tightQ1_82 using 1 <;> norm_num

theorem tightQ1_84 : TightBoxCovered (7 / 8) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 8) (1 / 8) (1 / 16) (1731123 / 2000000) (25701 / 250000) (143877 / 2000000) (10587 / 125000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_85 : TightBoxCovered (15 / 16) (1 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (15 / 16) (1 / 8) (1 / 16) (1731123 / 2000000) (25701 / 250000) (268877 / 2000000) (10587 / 125000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_86 : TightBoxCovered (7 / 8) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 8) (3 / 16) (1 / 16) (1731123 / 2000000) (25701 / 250000) (143877 / 2000000) (36799 / 250000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_87 : TightBoxCovered (15 / 16) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 16) (3 / 16) (1 / 32) (1731123 / 2000000) (25701 / 250000) (206377 / 2000000) (57973 / 500000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_88 : TightBoxCovered (31 / 32) (3 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 32) (3 / 16) (1 / 64) (1731123 / 2000000) (25701 / 250000) (237627 / 2000000) (100321 / 1000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_89 : TightBoxCovered (63 / 64) (3 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (63 / 64) (3 / 16) (1 / 64) (1731123 / 2000000) (25701 / 250000) (268877 / 2000000) (100321 / 1000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_90 : TightBoxCovered (31 / 32) (13 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 32) (13 / 64) (1 / 64) (1731123 / 2000000) (25701 / 250000) (237627 / 2000000) (57973 / 500000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_91 : TightBoxCovered (63 / 64) (13 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (63 / 64) (13 / 64) (1 / 128) (1731123 / 2000000) (25701 / 250000) (63313 / 500000) (216267 / 2000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_92 : TightBoxCovered (127 / 128) (13 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (127 / 128) (13 / 64) (1 / 256) (1731123 / 2000000) (25701 / 250000) (522129 / 4000000) (416909 / 4000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_93 : TightBoxCovered (255 / 256) (13 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (255 / 256) (13 / 64) (1 / 512) (1731123 / 2000000) (25701 / 250000) (1059883 / 8000000) (818193 / 8000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_94 : TightBoxCovered (511 / 512) (13 / 64) (1 / 512) := by
  apply tightBoxCovered_leaf (511 / 512) (13 / 64) (1 / 512) (1731123 / 2000000) (25701 / 250000) (268877 / 2000000) (818193 / 8000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_95 : TightBoxCovered (255 / 256) (105 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (255 / 256) (105 / 512) (1 / 512) (1731123 / 2000000) (25701 / 250000) (1059883 / 8000000) (416909 / 4000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_96 : TightBoxCovered (511 / 512) (105 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (511 / 512) (105 / 512) (1 / 1024) (1731123 / 2000000) (25701 / 250000) (2135391 / 16000000) (1652011 / 16000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_97 : TightBoxCovered (1023 / 1024) (105 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (1023 / 1024) (105 / 512) (1 / 1024) (1731123 / 2000000) (25701 / 250000) (268877 / 2000000) (1652011 / 16000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_98 : TightBoxCovered (511 / 512) (211 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (511 / 512) (211 / 1024) (1 / 1024) (1731123 / 2000000) (25701 / 250000) (2135391 / 16000000) (416909 / 4000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_99 : TightBoxCovered (1023 / 1024) (211 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (1023 / 1024) (211 / 1024) (1 / 1024) (445439 / 500000) (167763 / 500000) (54561 / 500000) (2071541 / 16000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_100 : TightBoxCovered (511 / 512) (105 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ1_96 using 1 <;> norm_num
  · convert tightQ1_97 using 1 <;> norm_num
  · convert tightQ1_98 using 1 <;> norm_num
  · convert tightQ1_99 using 1 <;> norm_num

theorem tightQ1_101 : TightBoxCovered (255 / 256) (13 / 64) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ1_93 using 1 <;> norm_num
  · convert tightQ1_94 using 1 <;> norm_num
  · convert tightQ1_95 using 1 <;> norm_num
  · convert tightQ1_100 using 1 <;> norm_num

theorem tightQ1_102 : TightBoxCovered (127 / 128) (53 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (127 / 128) (53 / 256) (1 / 256) (1731123 / 2000000) (25701 / 250000) (522129 / 4000000) (216267 / 2000000) ⟨3, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_103 : TightBoxCovered (255 / 256) (53 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (255 / 256) (53 / 256) (1 / 256) (445439 / 500000) (167763 / 500000) (54561 / 500000) (513979 / 4000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_104 : TightBoxCovered (127 / 128) (13 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_92 using 1 <;> norm_num
  · convert tightQ1_101 using 1 <;> norm_num
  · convert tightQ1_102 using 1 <;> norm_num
  · convert tightQ1_103 using 1 <;> norm_num

theorem tightQ1_105 : TightBoxCovered (63 / 64) (27 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (63 / 64) (27 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (202619 / 2000000) (249177 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_106 : TightBoxCovered (127 / 128) (27 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (127 / 128) (27 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (54561 / 500000) (249177 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_107 : TightBoxCovered (63 / 64) (13 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_91 using 1 <;> norm_num
  · convert tightQ1_104 using 1 <;> norm_num
  · convert tightQ1_105 using 1 <;> norm_num
  · convert tightQ1_106 using 1 <;> norm_num

theorem tightQ1_108 : TightBoxCovered (31 / 32) (3 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_88 using 1 <;> norm_num
  · convert tightQ1_89 using 1 <;> norm_num
  · convert tightQ1_90 using 1 <;> norm_num
  · convert tightQ1_107 using 1 <;> norm_num

theorem tightQ1_109 : TightBoxCovered (15 / 16) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 16) (7 / 32) (1 / 32) (445439 / 500000) (167763 / 500000) (4867 / 62500) (14597 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_110 : TightBoxCovered (31 / 32) (7 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (31 / 32) (7 / 32) (1 / 32) (445439 / 500000) (167763 / 500000) (54561 / 500000) (14597 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_111 : TightBoxCovered (15 / 16) (3 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_87 using 1 <;> norm_num
  · convert tightQ1_108 using 1 <;> norm_num
  · convert tightQ1_109 using 1 <;> norm_num
  · convert tightQ1_110 using 1 <;> norm_num

theorem tightQ1_112 : TightBoxCovered (7 / 8) (1 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_84 using 1 <;> norm_num
  · convert tightQ1_85 using 1 <;> norm_num
  · convert tightQ1_86 using 1 <;> norm_num
  · convert tightQ1_111 using 1 <;> norm_num

theorem tightQ1_113 : TightBoxCovered (3 / 4) 0 (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ1_65 using 1 <;> norm_num
  · convert tightQ1_66 using 1 <;> norm_num
  · convert tightQ1_83 using 1 <;> norm_num
  · convert tightQ1_112 using 1 <;> norm_num

theorem tightQ1_114 : TightBoxCovered (1 / 2) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (1 / 4) (1 / 64) (742311 / 2000000) (312933 / 1000000) (288939 / 2000000) (62933 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_115 : TightBoxCovered (33 / 64) (1 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (1 / 4) (1 / 128) (1267243 / 2000000) (34689 / 250000) (235993 / 2000000) (238113 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_116 : TightBoxCovered (67 / 128) (1 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (67 / 128) (1 / 4) (1 / 128) (1267243 / 2000000) (34689 / 250000) (13773 / 125000) (238113 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_117 : TightBoxCovered (33 / 64) (33 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (33 / 64) (33 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (76141 / 500000) (110241 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_118 : TightBoxCovered (67 / 128) (33 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (67 / 128) (33 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (13773 / 125000) (126869 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_119 : TightBoxCovered (33 / 64) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_115 using 1 <;> norm_num
  · convert tightQ1_116 using 1 <;> norm_num
  · convert tightQ1_117 using 1 <;> norm_num
  · convert tightQ1_118 using 1 <;> norm_num

theorem tightQ1_120 : TightBoxCovered (1 / 2) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (1 / 2) (17 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (288939 / 2000000) (11827 / 250000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_121 : TightBoxCovered (33 / 64) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (33 / 64) (17 / 64) (1 / 64) (742311 / 2000000) (312933 / 1000000) (320189 / 2000000) (11827 / 250000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_122 : TightBoxCovered (1 / 2) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_114 using 1 <;> norm_num
  · convert tightQ1_119 using 1 <;> norm_num
  · convert tightQ1_120 using 1 <;> norm_num
  · convert tightQ1_121 using 1 <;> norm_num

theorem tightQ1_123 : TightBoxCovered (17 / 32) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 32) (1 / 4) (1 / 64) (1267243 / 2000000) (34689 / 250000) (204743 / 2000000) (126869 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_124 : TightBoxCovered (35 / 64) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (1 / 4) (1 / 64) (1267243 / 2000000) (34689 / 250000) (173493 / 2000000) (126869 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_125 : TightBoxCovered (17 / 32) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 32) (17 / 64) (1 / 128) (1267243 / 2000000) (34689 / 250000) (204743 / 2000000) (269363 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_126 : TightBoxCovered (69 / 128) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (17 / 64) (1 / 128) (1267243 / 2000000) (34689 / 250000) (94559 / 1000000) (269363 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_127 : TightBoxCovered (17 / 32) (35 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 32) (35 / 128) (1 / 256) (742311 / 2000000) (312933 / 1000000) (656003 / 4000000) (78991 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_128 : TightBoxCovered (137 / 256) (35 / 128) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 256) (35 / 128) (1 / 512) (1267243 / 2000000) (34689 / 250000) (393861 / 4000000) (1093077 / 8000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_129 : TightBoxCovered (275 / 512) (35 / 128) (1 / 512) := by
  apply tightBoxCovered_leaf (275 / 512) (35 / 128) (1 / 512) (1267243 / 2000000) (34689 / 250000) (772097 / 8000000) (1093077 / 8000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_130 : TightBoxCovered (137 / 256) (141 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (137 / 256) (141 / 512) (1 / 1024) (1267243 / 2000000) (34689 / 250000) (393861 / 4000000) (2201779 / 16000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_131 : TightBoxCovered (549 / 1024) (141 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (549 / 1024) (141 / 512) (1 / 1024) (1267243 / 2000000) (34689 / 250000) (1559819 / 16000000) (2201779 / 16000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_132 : TightBoxCovered (137 / 256) (283 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (137 / 256) (283 / 1024) (1 / 1024) (742311 / 2000000) (312933 / 1000000) (2639637 / 16000000) (585053 / 16000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_133 : TightBoxCovered (549 / 1024) (283 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (549 / 1024) (283 / 1024) (1 / 1024) (1267243 / 2000000) (34689 / 250000) (1559819 / 16000000) (554351 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_134 : TightBoxCovered (137 / 256) (141 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ1_130 using 1 <;> norm_num
  · convert tightQ1_131 using 1 <;> norm_num
  · convert tightQ1_132 using 1 <;> norm_num
  · convert tightQ1_133 using 1 <;> norm_num

theorem tightQ1_135 : TightBoxCovered (275 / 512) (141 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (275 / 512) (141 / 512) (1 / 512) (1267243 / 2000000) (34689 / 250000) (772097 / 8000000) (554351 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_136 : TightBoxCovered (137 / 256) (35 / 128) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ1_128 using 1 <;> norm_num
  · convert tightQ1_129 using 1 <;> norm_num
  · convert tightQ1_134 using 1 <;> norm_num
  · convert tightQ1_135 using 1 <;> norm_num

theorem tightQ1_137 : TightBoxCovered (17 / 32) (71 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 32) (71 / 256) (1 / 256) (742311 / 2000000) (312933 / 1000000) (656003 / 4000000) (142357 / 4000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_138 : TightBoxCovered (137 / 256) (71 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 256) (71 / 256) (1 / 512) (742311 / 2000000) (312933 / 1000000) (1327631 / 8000000) (142357 / 4000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_139 : TightBoxCovered (275 / 512) (71 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (275 / 512) (71 / 256) (1 / 512) (635257 / 1000000) (166409 / 400000) (785181 / 8000000) (110943 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_140 : TightBoxCovered (137 / 256) (143 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (137 / 256) (143 / 512) (1 / 512) (742311 / 2000000) (312933 / 1000000) (1327631 / 8000000) (269089 / 8000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_141 : TightBoxCovered (275 / 512) (143 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (275 / 512) (143 / 512) (1 / 512) (635257 / 1000000) (166409 / 400000) (785181 / 8000000) (218761 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_142 : TightBoxCovered (137 / 256) (71 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ1_138 using 1 <;> norm_num
  · convert tightQ1_139 using 1 <;> norm_num
  · convert tightQ1_140 using 1 <;> norm_num
  · convert tightQ1_141 using 1 <;> norm_num

theorem tightQ1_143 : TightBoxCovered (17 / 32) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_127 using 1 <;> norm_num
  · convert tightQ1_136 using 1 <;> norm_num
  · convert tightQ1_137 using 1 <;> norm_num
  · convert tightQ1_142 using 1 <;> norm_num

theorem tightQ1_144 : TightBoxCovered (69 / 128) (35 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 128) (35 / 128) (1 / 256) (1267243 / 2000000) (34689 / 250000) (94559 / 1000000) (554351 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_145 : TightBoxCovered (139 / 256) (35 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (139 / 256) (35 / 128) (1 / 256) (1267243 / 2000000) (34689 / 250000) (362611 / 4000000) (554351 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_146 : TightBoxCovered (69 / 128) (71 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (69 / 128) (71 / 256) (1 / 256) (635257 / 1000000) (166409 / 400000) (192389 / 2000000) (110943 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_147 : TightBoxCovered (139 / 256) (71 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (139 / 256) (71 / 256) (1 / 256) (1267243 / 2000000) (34689 / 250000) (362611 / 4000000) (71247 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_148 : TightBoxCovered (69 / 128) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_144 using 1 <;> norm_num
  · convert tightQ1_145 using 1 <;> norm_num
  · convert tightQ1_146 using 1 <;> norm_num
  · convert tightQ1_147 using 1 <;> norm_num

theorem tightQ1_149 : TightBoxCovered (17 / 32) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_125 using 1 <;> norm_num
  · convert tightQ1_126 using 1 <;> norm_num
  · convert tightQ1_143 using 1 <;> norm_num
  · convert tightQ1_148 using 1 <;> norm_num

theorem tightQ1_150 : TightBoxCovered (35 / 64) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (17 / 64) (1 / 64) (1267243 / 2000000) (34689 / 250000) (173493 / 2000000) (71247 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_151 : TightBoxCovered (17 / 32) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_123 using 1 <;> norm_num
  · convert tightQ1_124 using 1 <;> norm_num
  · convert tightQ1_149 using 1 <;> norm_num
  · convert tightQ1_150 using 1 <;> norm_num

theorem tightQ1_152 : TightBoxCovered (1 / 2) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (9 / 32) (1 / 32) (742311 / 2000000) (312933 / 1000000) (320189 / 2000000) (31683 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_153 : TightBoxCovered (17 / 32) (9 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 32) (9 / 32) (1 / 256) (742311 / 2000000) (312933 / 1000000) (656003 / 4000000) (31683 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_154 : TightBoxCovered (137 / 256) (9 / 32) (1 / 256) := by
  apply tightBoxCovered_leaf (137 / 256) (9 / 32) (1 / 256) (635257 / 1000000) (166409 / 400000) (400403 / 4000000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_155 : TightBoxCovered (17 / 32) (73 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (17 / 32) (73 / 256) (1 / 256) (742311 / 2000000) (312933 / 1000000) (656003 / 4000000) (111107 / 4000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_156 : TightBoxCovered (137 / 256) (73 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (137 / 256) (73 / 256) (1 / 256) (635257 / 1000000) (166409 / 400000) (400403 / 4000000) (104693 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_157 : TightBoxCovered (17 / 32) (9 / 32) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_153 using 1 <;> norm_num
  · convert tightQ1_154 using 1 <;> norm_num
  · convert tightQ1_155 using 1 <;> norm_num
  · convert tightQ1_156 using 1 <;> norm_num

theorem tightQ1_158 : TightBoxCovered (69 / 128) (9 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (9 / 32) (1 / 128) (635257 / 1000000) (166409 / 400000) (192389 / 2000000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_159 : TightBoxCovered (17 / 32) (37 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (17 / 32) (37 / 128) (1 / 128) (742311 / 2000000) (312933 / 1000000) (167907 / 1000000) (47741 / 2000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_160 : TightBoxCovered (69 / 128) (37 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (69 / 128) (37 / 128) (1 / 128) (635257 / 1000000) (166409 / 400000) (192389 / 2000000) (1587 / 12500) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_161 : TightBoxCovered (17 / 32) (9 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_157 using 1 <;> norm_num
  · convert tightQ1_158 using 1 <;> norm_num
  · convert tightQ1_159 using 1 <;> norm_num
  · convert tightQ1_160 using 1 <;> norm_num

theorem tightQ1_162 : TightBoxCovered (35 / 64) (9 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (9 / 32) (1 / 64) (635257 / 1000000) (166409 / 400000) (44191 / 500000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_163 : TightBoxCovered (17 / 32) (19 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (17 / 32) (19 / 64) (1 / 64) (635257 / 1000000) (166409 / 400000) (104007 / 1000000) (47659 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_164 : TightBoxCovered (35 / 64) (19 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (35 / 64) (19 / 64) (1 / 64) (635257 / 1000000) (166409 / 400000) (44191 / 500000) (47659 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_165 : TightBoxCovered (17 / 32) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_161 using 1 <;> norm_num
  · convert tightQ1_162 using 1 <;> norm_num
  · convert tightQ1_163 using 1 <;> norm_num
  · convert tightQ1_164 using 1 <;> norm_num

theorem tightQ1_166 : TightBoxCovered (1 / 2) (1 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_122 using 1 <;> norm_num
  · convert tightQ1_151 using 1 <;> norm_num
  · convert tightQ1_152 using 1 <;> norm_num
  · convert tightQ1_165 using 1 <;> norm_num

theorem tightQ1_167 : TightBoxCovered (9 / 16) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 16) (1 / 4) (1 / 32) (1267243 / 2000000) (34689 / 250000) (142243 / 2000000) (71247 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_168 : TightBoxCovered (19 / 32) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (19 / 32) (1 / 4) (1 / 32) (1267243 / 2000000) (34689 / 250000) (79743 / 2000000) (71247 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_169 : TightBoxCovered (9 / 16) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (9 / 16) (9 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (72757 / 1000000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_170 : TightBoxCovered (19 / 32) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (19 / 32) (9 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (41507 / 1000000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_171 : TightBoxCovered (9 / 16) (1 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_167 using 1 <;> norm_num
  · convert tightQ1_168 using 1 <;> norm_num
  · convert tightQ1_169 using 1 <;> norm_num
  · convert tightQ1_170 using 1 <;> norm_num

theorem tightQ1_172 : TightBoxCovered (1 / 2) (5 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (5 / 16) (1 / 32) (742311 / 2000000) (312933 / 1000000) (320189 / 2000000) (30817 / 1000000) ⟨5, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_173 : TightBoxCovered (17 / 32) (5 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (5 / 16) (1 / 32) (635257 / 1000000) (166409 / 400000) (104007 / 1000000) (41409 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_174 : TightBoxCovered (1 / 2) (11 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (1 / 2) (11 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (135257 / 1000000) (28909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_175 : TightBoxCovered (17 / 32) (11 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (17 / 32) (11 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (104007 / 1000000) (28909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_176 : TightBoxCovered (1 / 2) (5 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_172 using 1 <;> norm_num
  · convert tightQ1_173 using 1 <;> norm_num
  · convert tightQ1_174 using 1 <;> norm_num
  · convert tightQ1_175 using 1 <;> norm_num

theorem tightQ1_177 : TightBoxCovered (9 / 16) (5 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (9 / 16) (5 / 16) (1 / 16) (635257 / 1000000) (166409 / 400000) (72757 / 1000000) (41409 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_178 : TightBoxCovered (1 / 2) (1 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_166 using 1 <;> norm_num
  · convert tightQ1_171 using 1 <;> norm_num
  · convert tightQ1_176 using 1 <;> norm_num
  · convert tightQ1_177 using 1 <;> norm_num

theorem tightQ1_179 : TightBoxCovered (5 / 8) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 8) (1 / 4) (1 / 32) (1267243 / 2000000) (34689 / 250000) (45257 / 2000000) (71247 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_180 : TightBoxCovered (21 / 32) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (21 / 32) (1 / 4) (1 / 32) (1267243 / 2000000) (34689 / 250000) (107757 / 2000000) (71247 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_181 : TightBoxCovered (5 / 8) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (5 / 8) (9 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (20993 / 1000000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_182 : TightBoxCovered (21 / 32) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (21 / 32) (9 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (52243 / 1000000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_183 : TightBoxCovered (5 / 8) (1 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_179 using 1 <;> norm_num
  · convert tightQ1_180 using 1 <;> norm_num
  · convert tightQ1_181 using 1 <;> norm_num
  · convert tightQ1_182 using 1 <;> norm_num

theorem tightQ1_184 : TightBoxCovered (11 / 16) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (1 / 4) (1 / 32) (1267243 / 2000000) (34689 / 250000) (170257 / 2000000) (71247 / 500000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_185 : TightBoxCovered (23 / 32) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (1 / 4) (1 / 64) (1267243 / 2000000) (34689 / 250000) (201507 / 2000000) (126869 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_186 : TightBoxCovered (47 / 64) (1 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (1 / 4) (1 / 128) (1267243 / 2000000) (34689 / 250000) (54283 / 500000) (238113 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_187 : TightBoxCovered (95 / 128) (1 / 4) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (1 / 4) (1 / 128) (1267243 / 2000000) (34689 / 250000) (232757 / 2000000) (238113 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_188 : TightBoxCovered (47 / 64) (33 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (33 / 128) (1 / 128) (1267243 / 2000000) (34689 / 250000) (54283 / 500000) (126869 / 1000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_189 : TightBoxCovered (95 / 128) (33 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (33 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (297381 / 2000000) (155427 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_190 : TightBoxCovered (47 / 64) (1 / 4) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_186 using 1 <;> norm_num
  · convert tightQ1_187 using 1 <;> norm_num
  · convert tightQ1_188 using 1 <;> norm_num
  · convert tightQ1_189 using 1 <;> norm_num

theorem tightQ1_191 : TightBoxCovered (23 / 32) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) (17 / 64) (1 / 128) (1267243 / 2000000) (34689 / 250000) (92941 / 1000000) (269363 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_192 : TightBoxCovered (93 / 128) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (93 / 128) (17 / 64) (1 / 128) (1267243 / 2000000) (34689 / 250000) (201507 / 2000000) (269363 / 2000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_193 : TightBoxCovered (23 / 32) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (23 / 32) (35 / 128) (1 / 128) (635257 / 1000000) (166409 / 400000) (182611 / 2000000) (28517 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_194 : TightBoxCovered (93 / 128) (35 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) (35 / 128) (1 / 256) (1267243 / 2000000) (34689 / 250000) (387389 / 4000000) (554351 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_195 : TightBoxCovered (187 / 256) (35 / 128) (1 / 512) := by
  apply tightBoxCovered_leaf (187 / 256) (35 / 128) (1 / 512) (1267243 / 2000000) (34689 / 250000) (790403 / 8000000) (1093077 / 8000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_196 : TightBoxCovered (375 / 512) (35 / 128) (1 / 512) := by
  apply tightBoxCovered_leaf (375 / 512) (35 / 128) (1 / 512) (1267243 / 2000000) (34689 / 250000) (201507 / 2000000) (1093077 / 8000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_197 : TightBoxCovered (187 / 256) (141 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (187 / 256) (141 / 512) (1 / 1024) (1267243 / 2000000) (34689 / 250000) (1565181 / 16000000) (2201779 / 16000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_198 : TightBoxCovered (749 / 1024) (141 / 512) (1 / 1024) := by
  apply tightBoxCovered_leaf (749 / 1024) (141 / 512) (1 / 1024) (1267243 / 2000000) (34689 / 250000) (790403 / 8000000) (2201779 / 16000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_199 : TightBoxCovered (187 / 256) (283 / 1024) (1 / 1024) := by
  apply tightBoxCovered_leaf (187 / 256) (283 / 1024) (1 / 1024) (1267243 / 2000000) (34689 / 250000) (1565181 / 16000000) (554351 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_200 : TightBoxCovered (749 / 1024) (283 / 1024) (1 / 2048) := by
  apply tightBoxCovered_leaf (749 / 1024) (283 / 1024) (1 / 2048) (1267243 / 2000000) (34689 / 250000) (3145987 / 32000000) (4419183 / 32000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_201 : TightBoxCovered (1499 / 2048) (283 / 1024) (1 / 2048) := by
  apply tightBoxCovered_leaf (1499 / 2048) (283 / 1024) (1 / 2048) (1267243 / 2000000) (34689 / 250000) (790403 / 8000000) (4419183 / 32000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_202 : TightBoxCovered (749 / 1024) (567 / 2048) (1 / 2048) := by
  apply tightBoxCovered_leaf (749 / 1024) (567 / 2048) (1 / 2048) (1267243 / 2000000) (34689 / 250000) (3145987 / 32000000) (554351 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_203 : TightBoxCovered (1499 / 2048) (567 / 2048) (1 / 2048) := by
  apply tightBoxCovered_leaf (1499 / 2048) (567 / 2048) (1 / 2048) (635257 / 1000000) (166409 / 400000) (777319 / 8000000) (890669 / 6400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_204 : TightBoxCovered (749 / 1024) (283 / 1024) (1 / 1024) := by
  apply tightBoxCovered_split
  · convert tightQ1_200 using 1 <;> norm_num
  · convert tightQ1_201 using 1 <;> norm_num
  · convert tightQ1_202 using 1 <;> norm_num
  · convert tightQ1_203 using 1 <;> norm_num

theorem tightQ1_205 : TightBoxCovered (187 / 256) (141 / 512) (1 / 512) := by
  apply tightBoxCovered_split
  · convert tightQ1_197 using 1 <;> norm_num
  · convert tightQ1_198 using 1 <;> norm_num
  · convert tightQ1_199 using 1 <;> norm_num
  · convert tightQ1_204 using 1 <;> norm_num

theorem tightQ1_206 : TightBoxCovered (375 / 512) (141 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (375 / 512) (141 / 512) (1 / 512) (445439 / 500000) (167763 / 500000) (1267649 / 8000000) (481083 / 8000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_207 : TightBoxCovered (187 / 256) (35 / 128) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ1_195 using 1 <;> norm_num
  · convert tightQ1_196 using 1 <;> norm_num
  · convert tightQ1_205 using 1 <;> norm_num
  · convert tightQ1_206 using 1 <;> norm_num

theorem tightQ1_208 : TightBoxCovered (93 / 128) (71 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (93 / 128) (71 / 256) (1 / 256) (635257 / 1000000) (166409 / 400000) (380847 / 4000000) (110943 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_209 : TightBoxCovered (187 / 256) (71 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (187 / 256) (71 / 256) (1 / 512) (635257 / 1000000) (166409 / 400000) (777319 / 8000000) (110943 / 800000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_210 : TightBoxCovered (375 / 512) (71 / 256) (1 / 512) := by
  apply tightBoxCovered_leaf (375 / 512) (71 / 256) (1 / 512) (445439 / 500000) (167763 / 500000) (1267649 / 8000000) (232729 / 4000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_211 : TightBoxCovered (187 / 256) (143 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (187 / 256) (143 / 512) (1 / 512) (635257 / 1000000) (166409 / 400000) (777319 / 8000000) (218761 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_212 : TightBoxCovered (375 / 512) (143 / 512) (1 / 512) := by
  apply tightBoxCovered_leaf (375 / 512) (143 / 512) (1 / 512) (635257 / 1000000) (166409 / 400000) (49559 / 500000) (218761 / 1600000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_213 : TightBoxCovered (187 / 256) (71 / 256) (1 / 256) := by
  apply tightBoxCovered_split
  · convert tightQ1_209 using 1 <;> norm_num
  · convert tightQ1_210 using 1 <;> norm_num
  · convert tightQ1_211 using 1 <;> norm_num
  · convert tightQ1_212 using 1 <;> norm_num

theorem tightQ1_214 : TightBoxCovered (93 / 128) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_194 using 1 <;> norm_num
  · convert tightQ1_207 using 1 <;> norm_num
  · convert tightQ1_208 using 1 <;> norm_num
  · convert tightQ1_213 using 1 <;> norm_num

theorem tightQ1_215 : TightBoxCovered (23 / 32) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_191 using 1 <;> norm_num
  · convert tightQ1_192 using 1 <;> norm_num
  · convert tightQ1_193 using 1 <;> norm_num
  · convert tightQ1_214 using 1 <;> norm_num

theorem tightQ1_216 : TightBoxCovered (47 / 64) (17 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (47 / 64) (17 / 64) (1 / 256) (1267243 / 2000000) (34689 / 250000) (418639 / 4000000) (523101 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_217 : TightBoxCovered (189 / 256) (17 / 64) (1 / 256) := by
  apply tightBoxCovered_leaf (189 / 256) (17 / 64) (1 / 256) (1267243 / 2000000) (34689 / 250000) (54283 / 500000) (523101 / 4000000) ⟨2, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_218 : TightBoxCovered (47 / 64) (69 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (47 / 64) (69 / 256) (1 / 256) (445439 / 500000) (167763 / 500000) (156503 / 1000000) (263979 / 4000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_219 : TightBoxCovered (189 / 256) (69 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (189 / 256) (69 / 256) (1 / 256) (445439 / 500000) (167763 / 500000) (610387 / 4000000) (263979 / 4000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_220 : TightBoxCovered (47 / 64) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_216 using 1 <;> norm_num
  · convert tightQ1_217 using 1 <;> norm_num
  · convert tightQ1_218 using 1 <;> norm_num
  · convert tightQ1_219 using 1 <;> norm_num

theorem tightQ1_221 : TightBoxCovered (95 / 128) (17 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (17 / 64) (1 / 128) (445439 / 500000) (167763 / 500000) (297381 / 2000000) (69901 / 1000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_222 : TightBoxCovered (47 / 64) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (47 / 64) (35 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (156503 / 1000000) (124177 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_223 : TightBoxCovered (95 / 128) (35 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (95 / 128) (35 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (297381 / 2000000) (124177 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_224 : TightBoxCovered (47 / 64) (17 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_220 using 1 <;> norm_num
  · convert tightQ1_221 using 1 <;> norm_num
  · convert tightQ1_222 using 1 <;> norm_num
  · convert tightQ1_223 using 1 <;> norm_num

theorem tightQ1_225 : TightBoxCovered (23 / 32) (1 / 4) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_185 using 1 <;> norm_num
  · convert tightQ1_190 using 1 <;> norm_num
  · convert tightQ1_215 using 1 <;> norm_num
  · convert tightQ1_224 using 1 <;> norm_num

theorem tightQ1_226 : TightBoxCovered (11 / 16) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (11 / 16) (9 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (83493 / 1000000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_227 : TightBoxCovered (23 / 32) (9 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (9 / 32) (1 / 64) (635257 / 1000000) (166409 / 400000) (49559 / 500000) (53909 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_228 : TightBoxCovered (47 / 64) (9 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (9 / 32) (1 / 64) (445439 / 500000) (167763 / 500000) (156503 / 1000000) (13569 / 250000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_229 : TightBoxCovered (23 / 32) (19 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (23 / 32) (19 / 64) (1 / 64) (635257 / 1000000) (166409 / 400000) (49559 / 500000) (47659 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_230 : TightBoxCovered (47 / 64) (19 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (47 / 64) (19 / 64) (1 / 64) (635257 / 1000000) (166409 / 400000) (114743 / 1000000) (47659 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_231 : TightBoxCovered (23 / 32) (9 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_227 using 1 <;> norm_num
  · convert tightQ1_228 using 1 <;> norm_num
  · convert tightQ1_229 using 1 <;> norm_num
  · convert tightQ1_230 using 1 <;> norm_num

theorem tightQ1_232 : TightBoxCovered (11 / 16) (1 / 4) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_184 using 1 <;> norm_num
  · convert tightQ1_225 using 1 <;> norm_num
  · convert tightQ1_226 using 1 <;> norm_num
  · convert tightQ1_231 using 1 <;> norm_num

theorem tightQ1_233 : TightBoxCovered (5 / 8) (5 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (5 / 8) (5 / 16) (1 / 16) (635257 / 1000000) (166409 / 400000) (52243 / 1000000) (41409 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_234 : TightBoxCovered (11 / 16) (5 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (11 / 16) (5 / 16) (1 / 16) (635257 / 1000000) (166409 / 400000) (114743 / 1000000) (41409 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_235 : TightBoxCovered (5 / 8) (1 / 4) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_183 using 1 <;> norm_num
  · convert tightQ1_232 using 1 <;> norm_num
  · convert tightQ1_233 using 1 <;> norm_num
  · convert tightQ1_234 using 1 <;> norm_num

theorem tightQ1_236 : TightBoxCovered (1 / 2) (3 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (1 / 2) (3 / 8) (1 / 8) (635257 / 1000000) (166409 / 400000) (135257 / 1000000) (33591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_237 : TightBoxCovered (5 / 8) (3 / 8) (1 / 8) := by
  apply tightBoxCovered_leaf (5 / 8) (3 / 8) (1 / 8) (635257 / 1000000) (166409 / 400000) (114743 / 1000000) (33591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_238 : TightBoxCovered (1 / 2) (1 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ1_178 using 1 <;> norm_num
  · convert tightQ1_235 using 1 <;> norm_num
  · convert tightQ1_236 using 1 <;> norm_num
  · convert tightQ1_237 using 1 <;> norm_num

theorem tightQ1_239 : TightBoxCovered (3 / 4) (1 / 4) (1 / 8) := by
  apply tightBoxCovered_leaf (3 / 4) (1 / 4) (1 / 8) (445439 / 500000) (167763 / 500000) (70439 / 500000) (42763 / 500000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_240 : TightBoxCovered (7 / 8) (1 / 4) (1 / 8) := by
  apply tightBoxCovered_leaf (7 / 8) (1 / 4) (1 / 8) (445439 / 500000) (167763 / 500000) (54561 / 500000) (42763 / 500000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_241 : TightBoxCovered (3 / 4) (3 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (3 / 8) (1 / 32) (635257 / 1000000) (166409 / 400000) (145993 / 1000000) (16409 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_242 : TightBoxCovered (25 / 32) (3 / 8) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (3 / 8) (1 / 32) (445439 / 500000) (167763 / 500000) (27407 / 250000) (17681 / 250000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_243 : TightBoxCovered (3 / 4) (13 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (13 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (145993 / 1000000) (8591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_244 : TightBoxCovered (25 / 32) (13 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (25 / 32) (13 / 32) (1 / 32) (445439 / 500000) (167763 / 500000) (27407 / 250000) (50987 / 500000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_245 : TightBoxCovered (3 / 4) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_241 using 1 <;> norm_num
  · convert tightQ1_242 using 1 <;> norm_num
  · convert tightQ1_243 using 1 <;> norm_num
  · convert tightQ1_244 using 1 <;> norm_num

theorem tightQ1_246 : TightBoxCovered (13 / 16) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (13 / 16) (3 / 8) (1 / 16) (445439 / 500000) (167763 / 500000) (39189 / 500000) (50987 / 500000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_247 : TightBoxCovered (3 / 4) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (7 / 16) (1 / 32) (635257 / 1000000) (166409 / 400000) (145993 / 1000000) (21091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_248 : TightBoxCovered (25 / 32) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (25 / 32) (7 / 16) (1 / 64) (635257 / 1000000) (166409 / 400000) (80809 / 500000) (14841 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_249 : TightBoxCovered (51 / 64) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (7 / 16) (1 / 64) (445439 / 500000) (167763 / 500000) (94003 / 1000000) (117599 / 1000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_250 : TightBoxCovered (25 / 32) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (29 / 64) (1 / 128) (635257 / 1000000) (166409 / 400000) (307611 / 2000000) (8983 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_251 : TightBoxCovered (101 / 128) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (29 / 64) (1 / 128) (635257 / 1000000) (166409 / 400000) (80809 / 500000) (8983 / 200000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_252 : TightBoxCovered (25 / 32) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (59 / 128) (1 / 128) (635257 / 1000000) (166409 / 400000) (307611 / 2000000) (21091 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_253 : TightBoxCovered (101 / 128) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (59 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (203631 / 2000000) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_254 : TightBoxCovered (25 / 32) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_250 using 1 <;> norm_num
  · convert tightQ1_251 using 1 <;> norm_num
  · convert tightQ1_252 using 1 <;> norm_num
  · convert tightQ1_253 using 1 <;> norm_num

theorem tightQ1_255 : TightBoxCovered (51 / 64) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (29 / 64) (1 / 64) (445439 / 500000) (167763 / 500000) (94003 / 1000000) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_256 : TightBoxCovered (25 / 32) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_248 using 1 <;> norm_num
  · convert tightQ1_249 using 1 <;> norm_num
  · convert tightQ1_254 using 1 <;> norm_num
  · convert tightQ1_255 using 1 <;> norm_num

theorem tightQ1_257 : TightBoxCovered (3 / 4) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (3 / 4) (15 / 32) (1 / 32) (635257 / 1000000) (166409 / 400000) (145993 / 1000000) (33591 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_258 : TightBoxCovered (25 / 32) (15 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (15 / 32) (1 / 128) (635257 / 1000000) (166409 / 400000) (307611 / 2000000) (3027 / 50000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_259 : TightBoxCovered (101 / 128) (15 / 32) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (15 / 32) (1 / 128) (1793819 / 2000000) (599621 / 1000000) (107847 / 1000000) (130871 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_260 : TightBoxCovered (25 / 32) (61 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (25 / 32) (61 / 128) (1 / 128) (635257 / 1000000) (166409 / 400000) (307611 / 2000000) (27341 / 400000) ⟨6, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_261 : TightBoxCovered (101 / 128) (61 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (101 / 128) (61 / 128) (1 / 128) (1793819 / 2000000) (599621 / 1000000) (107847 / 1000000) (246117 / 2000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_262 : TightBoxCovered (25 / 32) (15 / 32) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_258 using 1 <;> norm_num
  · convert tightQ1_259 using 1 <;> norm_num
  · convert tightQ1_260 using 1 <;> norm_num
  · convert tightQ1_261 using 1 <;> norm_num

theorem tightQ1_263 : TightBoxCovered (51 / 64) (15 / 32) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (15 / 32) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (200069 / 2000000) (130871 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_264 : TightBoxCovered (25 / 32) (31 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (25 / 32) (31 / 64) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (231319 / 2000000) (57623 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_265 : TightBoxCovered (51 / 64) (31 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (51 / 64) (31 / 64) (1 / 64) (1793819 / 2000000) (599621 / 1000000) (200069 / 2000000) (57623 / 500000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_266 : TightBoxCovered (25 / 32) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_262 using 1 <;> norm_num
  · convert tightQ1_263 using 1 <;> norm_num
  · convert tightQ1_264 using 1 <;> norm_num
  · convert tightQ1_265 using 1 <;> norm_num

theorem tightQ1_267 : TightBoxCovered (3 / 4) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_247 using 1 <;> norm_num
  · convert tightQ1_256 using 1 <;> norm_num
  · convert tightQ1_257 using 1 <;> norm_num
  · convert tightQ1_266 using 1 <;> norm_num

theorem tightQ1_268 : TightBoxCovered (13 / 16) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (13 / 16) (7 / 16) (1 / 32) (445439 / 500000) (167763 / 500000) (39189 / 500000) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_269 : TightBoxCovered (27 / 32) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (27 / 32) (7 / 16) (1 / 32) (445439 / 500000) (167763 / 500000) (5891 / 125000) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_270 : TightBoxCovered (13 / 16) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (13 / 16) (15 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (168819 / 2000000) (130871 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_271 : TightBoxCovered (27 / 32) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (27 / 32) (15 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (106319 / 2000000) (130871 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_272 : TightBoxCovered (13 / 16) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_268 using 1 <;> norm_num
  · convert tightQ1_269 using 1 <;> norm_num
  · convert tightQ1_270 using 1 <;> norm_num
  · convert tightQ1_271 using 1 <;> norm_num

theorem tightQ1_273 : TightBoxCovered (3 / 4) (3 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_245 using 1 <;> norm_num
  · convert tightQ1_246 using 1 <;> norm_num
  · convert tightQ1_267 using 1 <;> norm_num
  · convert tightQ1_272 using 1 <;> norm_num

theorem tightQ1_274 : TightBoxCovered (7 / 8) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 8) (3 / 8) (1 / 16) (445439 / 500000) (167763 / 500000) (23311 / 500000) (50987 / 500000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_275 : TightBoxCovered (15 / 16) (3 / 8) (1 / 16) := by
  apply tightBoxCovered_leaf (15 / 16) (3 / 8) (1 / 16) (445439 / 500000) (167763 / 500000) (54561 / 500000) (50987 / 500000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_276 : TightBoxCovered (7 / 8) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_leaf (7 / 8) (7 / 16) (1 / 16) (1793819 / 2000000) (599621 / 1000000) (81181 / 2000000) (162121 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_277 : TightBoxCovered (15 / 16) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 16) (7 / 16) (1 / 32) (445439 / 500000) (167763 / 500000) (4867 / 62500) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_278 : TightBoxCovered (31 / 32) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 32) (7 / 16) (1 / 64) (445439 / 500000) (167763 / 500000) (93497 / 1000000) (117599 / 1000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_279 : TightBoxCovered (63 / 64) (7 / 16) (1 / 64) := by
  apply tightBoxCovered_leaf (63 / 64) (7 / 16) (1 / 64) (445439 / 500000) (167763 / 500000) (54561 / 500000) (117599 / 1000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_280 : TightBoxCovered (31 / 32) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_leaf (31 / 32) (29 / 64) (1 / 64) (445439 / 500000) (167763 / 500000) (93497 / 1000000) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_281 : TightBoxCovered (63 / 64) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (63 / 64) (29 / 64) (1 / 128) (445439 / 500000) (167763 / 500000) (202619 / 2000000) (250823 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_282 : TightBoxCovered (127 / 128) (29 / 64) (1 / 128) := by
  apply tightBoxCovered_leaf (127 / 128) (29 / 64) (1 / 128) (445439 / 500000) (167763 / 500000) (54561 / 500000) (250823 / 2000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_283 : TightBoxCovered (63 / 64) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_leaf (63 / 64) (59 / 128) (1 / 128) (445439 / 500000) (167763 / 500000) (202619 / 2000000) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_284 : TightBoxCovered (127 / 128) (59 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (127 / 128) (59 / 128) (1 / 256) (445439 / 500000) (167763 / 500000) (420863 / 4000000) (517271 / 4000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_285 : TightBoxCovered (255 / 256) (59 / 128) (1 / 256) := by
  apply tightBoxCovered_leaf (255 / 256) (59 / 128) (1 / 256) (445439 / 500000) (167763 / 500000) (54561 / 500000) (517271 / 4000000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_286 : TightBoxCovered (127 / 128) (119 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (127 / 128) (119 / 256) (1 / 256) (445439 / 500000) (167763 / 500000) (420863 / 4000000) (16653 / 125000) ⟨7, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_287 : TightBoxCovered (255 / 256) (119 / 256) (1 / 256) := by
  apply tightBoxCovered_leaf (255 / 256) (119 / 256) (1 / 256) (1793819 / 2000000) (599621 / 1000000) (206181 / 2000000) (539109 / 4000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_288 : TightBoxCovered (127 / 128) (59 / 128) (1 / 128) := by
  apply tightBoxCovered_split
  · convert tightQ1_284 using 1 <;> norm_num
  · convert tightQ1_285 using 1 <;> norm_num
  · convert tightQ1_286 using 1 <;> norm_num
  · convert tightQ1_287 using 1 <;> norm_num

theorem tightQ1_289 : TightBoxCovered (63 / 64) (29 / 64) (1 / 64) := by
  apply tightBoxCovered_split
  · convert tightQ1_281 using 1 <;> norm_num
  · convert tightQ1_282 using 1 <;> norm_num
  · convert tightQ1_283 using 1 <;> norm_num
  · convert tightQ1_288 using 1 <;> norm_num

theorem tightQ1_290 : TightBoxCovered (31 / 32) (7 / 16) (1 / 32) := by
  apply tightBoxCovered_split
  · convert tightQ1_278 using 1 <;> norm_num
  · convert tightQ1_279 using 1 <;> norm_num
  · convert tightQ1_280 using 1 <;> norm_num
  · convert tightQ1_289 using 1 <;> norm_num

theorem tightQ1_291 : TightBoxCovered (15 / 16) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (15 / 16) (15 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (143681 / 2000000) (130871 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_292 : TightBoxCovered (31 / 32) (15 / 32) (1 / 32) := by
  apply tightBoxCovered_leaf (31 / 32) (15 / 32) (1 / 32) (1793819 / 2000000) (599621 / 1000000) (206181 / 2000000) (130871 / 1000000) ⟨11, by decide⟩ (by norm_num [coverSite]) <;> norm_num

theorem tightQ1_293 : TightBoxCovered (15 / 16) (7 / 16) (1 / 16) := by
  apply tightBoxCovered_split
  · convert tightQ1_277 using 1 <;> norm_num
  · convert tightQ1_290 using 1 <;> norm_num
  · convert tightQ1_291 using 1 <;> norm_num
  · convert tightQ1_292 using 1 <;> norm_num

theorem tightQ1_294 : TightBoxCovered (7 / 8) (3 / 8) (1 / 8) := by
  apply tightBoxCovered_split
  · convert tightQ1_274 using 1 <;> norm_num
  · convert tightQ1_275 using 1 <;> norm_num
  · convert tightQ1_276 using 1 <;> norm_num
  · convert tightQ1_293 using 1 <;> norm_num

theorem tightQ1_295 : TightBoxCovered (3 / 4) (1 / 4) (1 / 4) := by
  apply tightBoxCovered_split
  · convert tightQ1_239 using 1 <;> norm_num
  · convert tightQ1_240 using 1 <;> norm_num
  · convert tightQ1_273 using 1 <;> norm_num
  · convert tightQ1_294 using 1 <;> norm_num

theorem tightQ1_296 : TightBoxCovered (1 / 2) 0 (1 / 2) := by
  apply tightBoxCovered_split
  · convert tightQ1_64 using 1 <;> norm_num
  · convert tightQ1_113 using 1 <;> norm_num
  · convert tightQ1_238 using 1 <;> norm_num
  · convert tightQ1_295 using 1 <;> norm_num

theorem tightQuadrant1 : TightBoxCovered (1 / 2) 0 (1/2) := tightQ1_296

end ElevenSquare
