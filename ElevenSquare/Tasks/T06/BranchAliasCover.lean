import ElevenSquare.Tasks.T06.BranchAliasCover00
import ElevenSquare.Tasks.T06.BranchAliasCover01
import ElevenSquare.Tasks.T06.BranchAliasCover02
import ElevenSquare.Tasks.T06.BranchAliasCover03
import ElevenSquare.Tasks.T06.BranchAliasCover04
import ElevenSquare.Tasks.T06.BranchAliasCover05
import ElevenSquare.Tasks.T06.BranchAliasCover06
import ElevenSquare.Tasks.T06.BranchAliasCover07
import ElevenSquare.Tasks.T06.BranchAliasCover08
import ElevenSquare.Tasks.T06.BranchAliasCover09
import ElevenSquare.Tasks.T06.BranchAliasCover10
import ElevenSquare.Tasks.T06.BranchAliasCover11
import ElevenSquare.Tasks.T06.BranchAliasCover12
import ElevenSquare.Tasks.T06.BranchAliasCover13
import ElevenSquare.Tasks.T06.BranchAliasCover14
import ElevenSquare.Tasks.T06.BranchAliasCover15
import ElevenSquare.Tasks.T06.BranchAliasCover16
import ElevenSquare.Tasks.T06.BranchAliasCover17
import ElevenSquare.Tasks.T06.BranchAliasCover18
import ElevenSquare.Tasks.T06.BranchAliasCover19
import ElevenSquare.Tasks.T06.BranchAliasCover20
import ElevenSquare.Tasks.T06.BranchAliasCover21
import ElevenSquare.Tasks.T06.BranchAliasCover22
import ElevenSquare.Tasks.T06.BranchAliasCover23
import ElevenSquare.Tasks.T06.BranchAliasCover24
import ElevenSquare.Tasks.T06.BranchAliasCover25
import ElevenSquare.Tasks.T06.BranchAliasCover26
import ElevenSquare.Tasks.T06.BranchAliasCover27
import ElevenSquare.Tasks.T06.BranchAliasCover28
import ElevenSquare.Tasks.T06.BranchAliasCover29
import ElevenSquare.Tasks.T06.BranchAliasCover30
import ElevenSquare.Tasks.T06.BranchAliasCover31
import ElevenSquare.Tasks.T06.BranchSelection

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def rawGroupIndex (q : Fin 32) (s : Fin 16) : Fin 512 :=
  ⟨16*q.val+s.val, by have hq := q.isLt; have hs := s.isLt; omega⟩

theorem raw_group_cover_00 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 0 s)) row),
      RawEnabled (rawGroupIndex 0 s) g := by
  fin_cases s
  · exact raw_alias_cover_000
  · exact raw_alias_cover_001
  · exact raw_alias_cover_002
  · exact raw_alias_cover_003
  · exact raw_alias_cover_004
  · exact raw_alias_cover_005
  · exact raw_alias_cover_006
  · exact raw_alias_cover_007
  · exact raw_alias_cover_008
  · exact raw_alias_cover_009
  · exact raw_alias_cover_010
  · exact raw_alias_cover_011
  · exact raw_alias_cover_012
  · exact raw_alias_cover_013
  · exact raw_alias_cover_014
  · exact raw_alias_cover_015

theorem raw_group_cover_01 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 1 s)) row),
      RawEnabled (rawGroupIndex 1 s) g := by
  fin_cases s
  · exact raw_alias_cover_016
  · exact raw_alias_cover_017
  · exact raw_alias_cover_018
  · exact raw_alias_cover_019
  · exact raw_alias_cover_020
  · exact raw_alias_cover_021
  · exact raw_alias_cover_022
  · exact raw_alias_cover_023
  · exact raw_alias_cover_024
  · exact raw_alias_cover_025
  · exact raw_alias_cover_026
  · exact raw_alias_cover_027
  · exact raw_alias_cover_028
  · exact raw_alias_cover_029
  · exact raw_alias_cover_030
  · exact raw_alias_cover_031

theorem raw_group_cover_02 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 2 s)) row),
      RawEnabled (rawGroupIndex 2 s) g := by
  fin_cases s
  · exact raw_alias_cover_032
  · exact raw_alias_cover_033
  · exact raw_alias_cover_034
  · exact raw_alias_cover_035
  · exact raw_alias_cover_036
  · exact raw_alias_cover_037
  · exact raw_alias_cover_038
  · exact raw_alias_cover_039
  · exact raw_alias_cover_040
  · exact raw_alias_cover_041
  · exact raw_alias_cover_042
  · exact raw_alias_cover_043
  · exact raw_alias_cover_044
  · exact raw_alias_cover_045
  · exact raw_alias_cover_046
  · exact raw_alias_cover_047

theorem raw_group_cover_03 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 3 s)) row),
      RawEnabled (rawGroupIndex 3 s) g := by
  fin_cases s
  · exact raw_alias_cover_048
  · exact raw_alias_cover_049
  · exact raw_alias_cover_050
  · exact raw_alias_cover_051
  · exact raw_alias_cover_052
  · exact raw_alias_cover_053
  · exact raw_alias_cover_054
  · exact raw_alias_cover_055
  · exact raw_alias_cover_056
  · exact raw_alias_cover_057
  · exact raw_alias_cover_058
  · exact raw_alias_cover_059
  · exact raw_alias_cover_060
  · exact raw_alias_cover_061
  · exact raw_alias_cover_062
  · exact raw_alias_cover_063

theorem raw_group_cover_04 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 4 s)) row),
      RawEnabled (rawGroupIndex 4 s) g := by
  fin_cases s
  · exact raw_alias_cover_064
  · exact raw_alias_cover_065
  · exact raw_alias_cover_066
  · exact raw_alias_cover_067
  · exact raw_alias_cover_068
  · exact raw_alias_cover_069
  · exact raw_alias_cover_070
  · exact raw_alias_cover_071
  · exact raw_alias_cover_072
  · exact raw_alias_cover_073
  · exact raw_alias_cover_074
  · exact raw_alias_cover_075
  · exact raw_alias_cover_076
  · exact raw_alias_cover_077
  · exact raw_alias_cover_078
  · exact raw_alias_cover_079

theorem raw_group_cover_05 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 5 s)) row),
      RawEnabled (rawGroupIndex 5 s) g := by
  fin_cases s
  · exact raw_alias_cover_080
  · exact raw_alias_cover_081
  · exact raw_alias_cover_082
  · exact raw_alias_cover_083
  · exact raw_alias_cover_084
  · exact raw_alias_cover_085
  · exact raw_alias_cover_086
  · exact raw_alias_cover_087
  · exact raw_alias_cover_088
  · exact raw_alias_cover_089
  · exact raw_alias_cover_090
  · exact raw_alias_cover_091
  · exact raw_alias_cover_092
  · exact raw_alias_cover_093
  · exact raw_alias_cover_094
  · exact raw_alias_cover_095

theorem raw_group_cover_06 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 6 s)) row),
      RawEnabled (rawGroupIndex 6 s) g := by
  fin_cases s
  · exact raw_alias_cover_096
  · exact raw_alias_cover_097
  · exact raw_alias_cover_098
  · exact raw_alias_cover_099
  · exact raw_alias_cover_100
  · exact raw_alias_cover_101
  · exact raw_alias_cover_102
  · exact raw_alias_cover_103
  · exact raw_alias_cover_104
  · exact raw_alias_cover_105
  · exact raw_alias_cover_106
  · exact raw_alias_cover_107
  · exact raw_alias_cover_108
  · exact raw_alias_cover_109
  · exact raw_alias_cover_110
  · exact raw_alias_cover_111

theorem raw_group_cover_07 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 7 s)) row),
      RawEnabled (rawGroupIndex 7 s) g := by
  fin_cases s
  · exact raw_alias_cover_112
  · exact raw_alias_cover_113
  · exact raw_alias_cover_114
  · exact raw_alias_cover_115
  · exact raw_alias_cover_116
  · exact raw_alias_cover_117
  · exact raw_alias_cover_118
  · exact raw_alias_cover_119
  · exact raw_alias_cover_120
  · exact raw_alias_cover_121
  · exact raw_alias_cover_122
  · exact raw_alias_cover_123
  · exact raw_alias_cover_124
  · exact raw_alias_cover_125
  · exact raw_alias_cover_126
  · exact raw_alias_cover_127

theorem raw_group_cover_08 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 8 s)) row),
      RawEnabled (rawGroupIndex 8 s) g := by
  fin_cases s
  · exact raw_alias_cover_128
  · exact raw_alias_cover_129
  · exact raw_alias_cover_130
  · exact raw_alias_cover_131
  · exact raw_alias_cover_132
  · exact raw_alias_cover_133
  · exact raw_alias_cover_134
  · exact raw_alias_cover_135
  · exact raw_alias_cover_136
  · exact raw_alias_cover_137
  · exact raw_alias_cover_138
  · exact raw_alias_cover_139
  · exact raw_alias_cover_140
  · exact raw_alias_cover_141
  · exact raw_alias_cover_142
  · exact raw_alias_cover_143

theorem raw_group_cover_09 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 9 s)) row),
      RawEnabled (rawGroupIndex 9 s) g := by
  fin_cases s
  · exact raw_alias_cover_144
  · exact raw_alias_cover_145
  · exact raw_alias_cover_146
  · exact raw_alias_cover_147
  · exact raw_alias_cover_148
  · exact raw_alias_cover_149
  · exact raw_alias_cover_150
  · exact raw_alias_cover_151
  · exact raw_alias_cover_152
  · exact raw_alias_cover_153
  · exact raw_alias_cover_154
  · exact raw_alias_cover_155
  · exact raw_alias_cover_156
  · exact raw_alias_cover_157
  · exact raw_alias_cover_158
  · exact raw_alias_cover_159

theorem raw_group_cover_10 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 10 s)) row),
      RawEnabled (rawGroupIndex 10 s) g := by
  fin_cases s
  · exact raw_alias_cover_160
  · exact raw_alias_cover_161
  · exact raw_alias_cover_162
  · exact raw_alias_cover_163
  · exact raw_alias_cover_164
  · exact raw_alias_cover_165
  · exact raw_alias_cover_166
  · exact raw_alias_cover_167
  · exact raw_alias_cover_168
  · exact raw_alias_cover_169
  · exact raw_alias_cover_170
  · exact raw_alias_cover_171
  · exact raw_alias_cover_172
  · exact raw_alias_cover_173
  · exact raw_alias_cover_174
  · exact raw_alias_cover_175

theorem raw_group_cover_11 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 11 s)) row),
      RawEnabled (rawGroupIndex 11 s) g := by
  fin_cases s
  · exact raw_alias_cover_176
  · exact raw_alias_cover_177
  · exact raw_alias_cover_178
  · exact raw_alias_cover_179
  · exact raw_alias_cover_180
  · exact raw_alias_cover_181
  · exact raw_alias_cover_182
  · exact raw_alias_cover_183
  · exact raw_alias_cover_184
  · exact raw_alias_cover_185
  · exact raw_alias_cover_186
  · exact raw_alias_cover_187
  · exact raw_alias_cover_188
  · exact raw_alias_cover_189
  · exact raw_alias_cover_190
  · exact raw_alias_cover_191

theorem raw_group_cover_12 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 12 s)) row),
      RawEnabled (rawGroupIndex 12 s) g := by
  fin_cases s
  · exact raw_alias_cover_192
  · exact raw_alias_cover_193
  · exact raw_alias_cover_194
  · exact raw_alias_cover_195
  · exact raw_alias_cover_196
  · exact raw_alias_cover_197
  · exact raw_alias_cover_198
  · exact raw_alias_cover_199
  · exact raw_alias_cover_200
  · exact raw_alias_cover_201
  · exact raw_alias_cover_202
  · exact raw_alias_cover_203
  · exact raw_alias_cover_204
  · exact raw_alias_cover_205
  · exact raw_alias_cover_206
  · exact raw_alias_cover_207

theorem raw_group_cover_13 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 13 s)) row),
      RawEnabled (rawGroupIndex 13 s) g := by
  fin_cases s
  · exact raw_alias_cover_208
  · exact raw_alias_cover_209
  · exact raw_alias_cover_210
  · exact raw_alias_cover_211
  · exact raw_alias_cover_212
  · exact raw_alias_cover_213
  · exact raw_alias_cover_214
  · exact raw_alias_cover_215
  · exact raw_alias_cover_216
  · exact raw_alias_cover_217
  · exact raw_alias_cover_218
  · exact raw_alias_cover_219
  · exact raw_alias_cover_220
  · exact raw_alias_cover_221
  · exact raw_alias_cover_222
  · exact raw_alias_cover_223

theorem raw_group_cover_14 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 14 s)) row),
      RawEnabled (rawGroupIndex 14 s) g := by
  fin_cases s
  · exact raw_alias_cover_224
  · exact raw_alias_cover_225
  · exact raw_alias_cover_226
  · exact raw_alias_cover_227
  · exact raw_alias_cover_228
  · exact raw_alias_cover_229
  · exact raw_alias_cover_230
  · exact raw_alias_cover_231
  · exact raw_alias_cover_232
  · exact raw_alias_cover_233
  · exact raw_alias_cover_234
  · exact raw_alias_cover_235
  · exact raw_alias_cover_236
  · exact raw_alias_cover_237
  · exact raw_alias_cover_238
  · exact raw_alias_cover_239

theorem raw_group_cover_15 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 15 s)) row),
      RawEnabled (rawGroupIndex 15 s) g := by
  fin_cases s
  · exact raw_alias_cover_240
  · exact raw_alias_cover_241
  · exact raw_alias_cover_242
  · exact raw_alias_cover_243
  · exact raw_alias_cover_244
  · exact raw_alias_cover_245
  · exact raw_alias_cover_246
  · exact raw_alias_cover_247
  · exact raw_alias_cover_248
  · exact raw_alias_cover_249
  · exact raw_alias_cover_250
  · exact raw_alias_cover_251
  · exact raw_alias_cover_252
  · exact raw_alias_cover_253
  · exact raw_alias_cover_254
  · exact raw_alias_cover_255

theorem raw_group_cover_16 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 16 s)) row),
      RawEnabled (rawGroupIndex 16 s) g := by
  fin_cases s
  · exact raw_alias_cover_256
  · exact raw_alias_cover_257
  · exact raw_alias_cover_258
  · exact raw_alias_cover_259
  · exact raw_alias_cover_260
  · exact raw_alias_cover_261
  · exact raw_alias_cover_262
  · exact raw_alias_cover_263
  · exact raw_alias_cover_264
  · exact raw_alias_cover_265
  · exact raw_alias_cover_266
  · exact raw_alias_cover_267
  · exact raw_alias_cover_268
  · exact raw_alias_cover_269
  · exact raw_alias_cover_270
  · exact raw_alias_cover_271

theorem raw_group_cover_17 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 17 s)) row),
      RawEnabled (rawGroupIndex 17 s) g := by
  fin_cases s
  · exact raw_alias_cover_272
  · exact raw_alias_cover_273
  · exact raw_alias_cover_274
  · exact raw_alias_cover_275
  · exact raw_alias_cover_276
  · exact raw_alias_cover_277
  · exact raw_alias_cover_278
  · exact raw_alias_cover_279
  · exact raw_alias_cover_280
  · exact raw_alias_cover_281
  · exact raw_alias_cover_282
  · exact raw_alias_cover_283
  · exact raw_alias_cover_284
  · exact raw_alias_cover_285
  · exact raw_alias_cover_286
  · exact raw_alias_cover_287

theorem raw_group_cover_18 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 18 s)) row),
      RawEnabled (rawGroupIndex 18 s) g := by
  fin_cases s
  · exact raw_alias_cover_288
  · exact raw_alias_cover_289
  · exact raw_alias_cover_290
  · exact raw_alias_cover_291
  · exact raw_alias_cover_292
  · exact raw_alias_cover_293
  · exact raw_alias_cover_294
  · exact raw_alias_cover_295
  · exact raw_alias_cover_296
  · exact raw_alias_cover_297
  · exact raw_alias_cover_298
  · exact raw_alias_cover_299
  · exact raw_alias_cover_300
  · exact raw_alias_cover_301
  · exact raw_alias_cover_302
  · exact raw_alias_cover_303

theorem raw_group_cover_19 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 19 s)) row),
      RawEnabled (rawGroupIndex 19 s) g := by
  fin_cases s
  · exact raw_alias_cover_304
  · exact raw_alias_cover_305
  · exact raw_alias_cover_306
  · exact raw_alias_cover_307
  · exact raw_alias_cover_308
  · exact raw_alias_cover_309
  · exact raw_alias_cover_310
  · exact raw_alias_cover_311
  · exact raw_alias_cover_312
  · exact raw_alias_cover_313
  · exact raw_alias_cover_314
  · exact raw_alias_cover_315
  · exact raw_alias_cover_316
  · exact raw_alias_cover_317
  · exact raw_alias_cover_318
  · exact raw_alias_cover_319

theorem raw_group_cover_20 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 20 s)) row),
      RawEnabled (rawGroupIndex 20 s) g := by
  fin_cases s
  · exact raw_alias_cover_320
  · exact raw_alias_cover_321
  · exact raw_alias_cover_322
  · exact raw_alias_cover_323
  · exact raw_alias_cover_324
  · exact raw_alias_cover_325
  · exact raw_alias_cover_326
  · exact raw_alias_cover_327
  · exact raw_alias_cover_328
  · exact raw_alias_cover_329
  · exact raw_alias_cover_330
  · exact raw_alias_cover_331
  · exact raw_alias_cover_332
  · exact raw_alias_cover_333
  · exact raw_alias_cover_334
  · exact raw_alias_cover_335

theorem raw_group_cover_21 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 21 s)) row),
      RawEnabled (rawGroupIndex 21 s) g := by
  fin_cases s
  · exact raw_alias_cover_336
  · exact raw_alias_cover_337
  · exact raw_alias_cover_338
  · exact raw_alias_cover_339
  · exact raw_alias_cover_340
  · exact raw_alias_cover_341
  · exact raw_alias_cover_342
  · exact raw_alias_cover_343
  · exact raw_alias_cover_344
  · exact raw_alias_cover_345
  · exact raw_alias_cover_346
  · exact raw_alias_cover_347
  · exact raw_alias_cover_348
  · exact raw_alias_cover_349
  · exact raw_alias_cover_350
  · exact raw_alias_cover_351

theorem raw_group_cover_22 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 22 s)) row),
      RawEnabled (rawGroupIndex 22 s) g := by
  fin_cases s
  · exact raw_alias_cover_352
  · exact raw_alias_cover_353
  · exact raw_alias_cover_354
  · exact raw_alias_cover_355
  · exact raw_alias_cover_356
  · exact raw_alias_cover_357
  · exact raw_alias_cover_358
  · exact raw_alias_cover_359
  · exact raw_alias_cover_360
  · exact raw_alias_cover_361
  · exact raw_alias_cover_362
  · exact raw_alias_cover_363
  · exact raw_alias_cover_364
  · exact raw_alias_cover_365
  · exact raw_alias_cover_366
  · exact raw_alias_cover_367

theorem raw_group_cover_23 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 23 s)) row),
      RawEnabled (rawGroupIndex 23 s) g := by
  fin_cases s
  · exact raw_alias_cover_368
  · exact raw_alias_cover_369
  · exact raw_alias_cover_370
  · exact raw_alias_cover_371
  · exact raw_alias_cover_372
  · exact raw_alias_cover_373
  · exact raw_alias_cover_374
  · exact raw_alias_cover_375
  · exact raw_alias_cover_376
  · exact raw_alias_cover_377
  · exact raw_alias_cover_378
  · exact raw_alias_cover_379
  · exact raw_alias_cover_380
  · exact raw_alias_cover_381
  · exact raw_alias_cover_382
  · exact raw_alias_cover_383

theorem raw_group_cover_24 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 24 s)) row),
      RawEnabled (rawGroupIndex 24 s) g := by
  fin_cases s
  · exact raw_alias_cover_384
  · exact raw_alias_cover_385
  · exact raw_alias_cover_386
  · exact raw_alias_cover_387
  · exact raw_alias_cover_388
  · exact raw_alias_cover_389
  · exact raw_alias_cover_390
  · exact raw_alias_cover_391
  · exact raw_alias_cover_392
  · exact raw_alias_cover_393
  · exact raw_alias_cover_394
  · exact raw_alias_cover_395
  · exact raw_alias_cover_396
  · exact raw_alias_cover_397
  · exact raw_alias_cover_398
  · exact raw_alias_cover_399

theorem raw_group_cover_25 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 25 s)) row),
      RawEnabled (rawGroupIndex 25 s) g := by
  fin_cases s
  · exact raw_alias_cover_400
  · exact raw_alias_cover_401
  · exact raw_alias_cover_402
  · exact raw_alias_cover_403
  · exact raw_alias_cover_404
  · exact raw_alias_cover_405
  · exact raw_alias_cover_406
  · exact raw_alias_cover_407
  · exact raw_alias_cover_408
  · exact raw_alias_cover_409
  · exact raw_alias_cover_410
  · exact raw_alias_cover_411
  · exact raw_alias_cover_412
  · exact raw_alias_cover_413
  · exact raw_alias_cover_414
  · exact raw_alias_cover_415

theorem raw_group_cover_26 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 26 s)) row),
      RawEnabled (rawGroupIndex 26 s) g := by
  fin_cases s
  · exact raw_alias_cover_416
  · exact raw_alias_cover_417
  · exact raw_alias_cover_418
  · exact raw_alias_cover_419
  · exact raw_alias_cover_420
  · exact raw_alias_cover_421
  · exact raw_alias_cover_422
  · exact raw_alias_cover_423
  · exact raw_alias_cover_424
  · exact raw_alias_cover_425
  · exact raw_alias_cover_426
  · exact raw_alias_cover_427
  · exact raw_alias_cover_428
  · exact raw_alias_cover_429
  · exact raw_alias_cover_430
  · exact raw_alias_cover_431

theorem raw_group_cover_27 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 27 s)) row),
      RawEnabled (rawGroupIndex 27 s) g := by
  fin_cases s
  · exact raw_alias_cover_432
  · exact raw_alias_cover_433
  · exact raw_alias_cover_434
  · exact raw_alias_cover_435
  · exact raw_alias_cover_436
  · exact raw_alias_cover_437
  · exact raw_alias_cover_438
  · exact raw_alias_cover_439
  · exact raw_alias_cover_440
  · exact raw_alias_cover_441
  · exact raw_alias_cover_442
  · exact raw_alias_cover_443
  · exact raw_alias_cover_444
  · exact raw_alias_cover_445
  · exact raw_alias_cover_446
  · exact raw_alias_cover_447

theorem raw_group_cover_28 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 28 s)) row),
      RawEnabled (rawGroupIndex 28 s) g := by
  fin_cases s
  · exact raw_alias_cover_448
  · exact raw_alias_cover_449
  · exact raw_alias_cover_450
  · exact raw_alias_cover_451
  · exact raw_alias_cover_452
  · exact raw_alias_cover_453
  · exact raw_alias_cover_454
  · exact raw_alias_cover_455
  · exact raw_alias_cover_456
  · exact raw_alias_cover_457
  · exact raw_alias_cover_458
  · exact raw_alias_cover_459
  · exact raw_alias_cover_460
  · exact raw_alias_cover_461
  · exact raw_alias_cover_462
  · exact raw_alias_cover_463

theorem raw_group_cover_29 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 29 s)) row),
      RawEnabled (rawGroupIndex 29 s) g := by
  fin_cases s
  · exact raw_alias_cover_464
  · exact raw_alias_cover_465
  · exact raw_alias_cover_466
  · exact raw_alias_cover_467
  · exact raw_alias_cover_468
  · exact raw_alias_cover_469
  · exact raw_alias_cover_470
  · exact raw_alias_cover_471
  · exact raw_alias_cover_472
  · exact raw_alias_cover_473
  · exact raw_alias_cover_474
  · exact raw_alias_cover_475
  · exact raw_alias_cover_476
  · exact raw_alias_cover_477
  · exact raw_alias_cover_478
  · exact raw_alias_cover_479

theorem raw_group_cover_30 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 30 s)) row),
      RawEnabled (rawGroupIndex 30 s) g := by
  fin_cases s
  · exact raw_alias_cover_480
  · exact raw_alias_cover_481
  · exact raw_alias_cover_482
  · exact raw_alias_cover_483
  · exact raw_alias_cover_484
  · exact raw_alias_cover_485
  · exact raw_alias_cover_486
  · exact raw_alias_cover_487
  · exact raw_alias_cover_488
  · exact raw_alias_cover_489
  · exact raw_alias_cover_490
  · exact raw_alias_cover_491
  · exact raw_alias_cover_492
  · exact raw_alias_cover_493
  · exact raw_alias_cover_494
  · exact raw_alias_cover_495

theorem raw_group_cover_31 (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex 31 s)) row),
      RawEnabled (rawGroupIndex 31 s) g := by
  fin_cases s
  · exact raw_alias_cover_496
  · exact raw_alias_cover_497
  · exact raw_alias_cover_498
  · exact raw_alias_cover_499
  · exact raw_alias_cover_500
  · exact raw_alias_cover_501
  · exact raw_alias_cover_502
  · exact raw_alias_cover_503
  · exact raw_alias_cover_504
  · exact raw_alias_cover_505
  · exact raw_alias_cover_506
  · exact raw_alias_cover_507
  · exact raw_alias_cover_508
  · exact raw_alias_cover_509
  · exact raw_alias_cover_510
  · exact raw_alias_cover_511

theorem rawGroupCover (q : Fin 32) (s : Fin 16) :
    ∀ row : Fin 42, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch (rawGroupIndex q s)) row),
      RawEnabled (rawGroupIndex q s) g := by
  fin_cases q
  · exact raw_group_cover_00 s
  · exact raw_group_cover_01 s
  · exact raw_group_cover_02 s
  · exact raw_group_cover_03 s
  · exact raw_group_cover_04 s
  · exact raw_group_cover_05 s
  · exact raw_group_cover_06 s
  · exact raw_group_cover_07 s
  · exact raw_group_cover_08 s
  · exact raw_group_cover_09 s
  · exact raw_group_cover_10 s
  · exact raw_group_cover_11 s
  · exact raw_group_cover_12 s
  · exact raw_group_cover_13 s
  · exact raw_group_cover_14 s
  · exact raw_group_cover_15 s
  · exact raw_group_cover_16 s
  · exact raw_group_cover_17 s
  · exact raw_group_cover_18 s
  · exact raw_group_cover_19 s
  · exact raw_group_cover_20 s
  · exact raw_group_cover_21 s
  · exact raw_group_cover_22 s
  · exact raw_group_cover_23 s
  · exact raw_group_cover_24 s
  · exact raw_group_cover_25 s
  · exact raw_group_cover_26 s
  · exact raw_group_cover_27 s
  · exact raw_group_cover_28 s
  · exact raw_group_cover_29 s
  · exact raw_group_cover_30 s
  · exact raw_group_cover_31 s

theorem rawSelection_alias_cover :
    ∀ r : Fin 512, ∀ row : Fin 42,
      ∃ g ∈ rowAliases (branchRows (rawSelectionBranch r) row), RawEnabled r g := by
  intro r
  let q : Fin 32 := ⟨r.val / 16, by have hr := r.isLt; omega⟩
  let s : Fin 16 := ⟨r.val % 16, Nat.mod_lt _ (by decide)⟩
  have hr : rawGroupIndex q s = r := by
    apply Fin.ext
    dsimp [rawGroupIndex, q, s]
    omega
  rw [← hr]
  exact rawGroupCover q s

end
end ElevenSquare.Tasks.T06
