import ElevenSquare.ConstructionData

namespace ElevenSquare.Pending.T06
noncomputable section

@[simp] theorem constructionCenter_eval_00 : constructionCenter 0 = ((1 / 2), (1 / 2)) := rfl

@[simp] theorem constructionCenter_eval_01 : constructionCenter 1 = ((25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2, (1 / 2)) := rfl

@[simp] theorem constructionCenter_eval_02 : constructionCenter 2 = ((5 / 2) * u^7 - (25 / 4) * u^6 + (3 / 2) * u^5 + (15 / 2) * u^4 + (5 / 2) * u^3 - (19 / 4) * u^2 + (5 / 2) * u + 2, (25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) := rfl

@[simp] theorem constructionCenter_eval_03 : constructionCenter 3 = ((1 / 2), (25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) := rfl

@[simp] theorem constructionCenter_eval_04 : constructionCenter 4 = ((3 / 2), (25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 2) := rfl

@[simp] theorem constructionCenter_eval_05 : constructionCenter 5 = ((1 / 2), (25 / 8) * u^7 - (15 / 2) * u^6 + (15 / 8) * u^5 + 8 * u^4 + (35 / 8) * u^3 - 5 * u^2 + (37 / 8) * u + 1) := rfl

@[simp] theorem constructionCenter_eval_06 : constructionCenter 6 = ((147 / 80) * u^7 - (75 / 16) * u^6 + (581 / 400) * u^5 + (419 / 80) * u^4 + (729 / 400) * u^3 - (1549 / 400) * u^2 + (771 / 400) * u + (361 / 400), (79 / 80) * u^7 - (45 / 16) * u^6 + (717 / 400) * u^5 + (173 / 80) * u^4 + (53 / 400) * u^3 - (843 / 400) * u^2 + (947 / 400) * u + (327 / 400)) := rfl

@[simp] theorem constructionCenter_eval_07 : constructionCenter 7 = ((53 / 16) * u^7 - (125 / 16) * u^6 + (119 / 80) * u^5 + (141 / 16) * u^4 + (431 / 80) * u^3 - (471 / 80) * u^2 + (289 / 80) * u + (79 / 80), (1 / 16) * u^7 - (5 / 16) * u^6 + (23 / 80) * u^5 + (9 / 16) * u^4 - (53 / 80) * u^3 - (87 / 80) * u^2 + (73 / 80) * u + (43 / 80)) := rfl

@[simp] theorem constructionCenter_eval_08 : constructionCenter 8 = ((113 / 80) * u^7 - (45 / 16) * u^6 - (101 / 400) * u^5 + (241 / 80) * u^4 + (1691 / 400) * u^3 - (371 / 400) * u^2 + (309 / 400) * u + (619 / 400), (191 / 80) * u^7 - (85 / 16) * u^6 - (7 / 400) * u^5 + (577 / 80) * u^4 + (1837 / 400) * u^3 - (1947 / 400) * u^2 + (863 / 400) * u + (683 / 400)) := rfl

@[simp] theorem constructionCenter_eval_09 : constructionCenter 9 = ((231 / 80) * u^7 - (95 / 16) * u^6 - (87 / 400) * u^5 + (527 / 80) * u^4 + (3117 / 400) * u^3 - (1177 / 400) * u^2 + (983 / 400) * u + (653 / 400), (117 / 80) * u^7 - (45 / 16) * u^6 - (609 / 400) * u^5 + (449 / 80) * u^4 + (1519 / 400) * u^3 - (1539 / 400) * u^2 + (281 / 400) * u + (571 / 400)) := rfl

@[simp] theorem constructionCenter_eval_10 : constructionCenter 10 = ((49 / 16) * u^7 - (115 / 16) * u^6 + (127 / 80) * u^5 + (119 / 16) * u^4 + (403 / 80) * u^3 - (313 / 80) * u^2 + (297 / 80) * u + (157 / 80), (43 / 16) * u^7 - (85 / 16) * u^6 - (111 / 80) * u^5 + (125 / 16) * u^4 + (561 / 80) * u^3 - (311 / 80) * u^2 + (199 / 80) * u + (119 / 80)) := rfl

end
end ElevenSquare.Pending.T06
