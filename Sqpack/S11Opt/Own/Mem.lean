import Sqpack.S11Opt.Own.o0_3317172372_4284871135
import Sqpack.S11Opt.Own.o0_3444858613_3789958499
import Sqpack.S11Opt.Own.o0_3466333470_3789958499
import Sqpack.S11Opt.Own.o0_4277969138_3746952623
import Sqpack.S11Opt.Own.o0_4277969138_4284871135
import Sqpack.S11Opt.Own.o1_6751901432_3990372141
import Sqpack.S11Opt.Own.o1_6759139717_2709765890
import Sqpack.S11Opt.Own.o1_6887576451_2748363060
import Sqpack.S11Opt.Own.o2_9614869580_4286313812
import Sqpack.S11Opt.Own.o2_9643989460_4178888280
import Sqpack.S11Opt.Own.o2_9729412683_3997255438
import Sqpack.S11Opt.Own.o2_9976778687_3798547165
import Sqpack.S11Opt.Own.o2_9977141320_3862092438
import Sqpack.S11Opt.Own.o3_12366716317_3090563892
import Sqpack.S11Opt.Own.o3_12366716317_4277428641
import Sqpack.S11Opt.Own.o3_12843221977_3417833872
import Sqpack.S11Opt.Own.o3_12982957438_4277428641
import Sqpack.S11Opt.Own.o3_13028053680_4174883416
import Sqpack.S11Opt.Own.o4_3421374150_7094965680
import Sqpack.S11Opt.Own.o4_3442849007_7094965680
import Sqpack.S11Opt.Own.o4_3728252507_7355438087
import Sqpack.S11Opt.Own.o4_4277499448_7047558535
import Sqpack.S11Opt.Own.o4_4277499448_7130692521
import Sqpack.S11Opt.Own.o5_6733851133_6014396183
import Sqpack.S11Opt.Own.o5_6734642089_5948857046
import Sqpack.S11Opt.Own.o8_3476074262_10265546617
import Sqpack.S11Opt.Own.o8_3495905346_10358385407
import Sqpack.S11Opt.Own.o8_3561497485_10083913776
import Sqpack.S11Opt.Own.o8_3686124094_9976131924
import Sqpack.S11Opt.Own.o8_4278990070_10189603028
import Sqpack.S11Opt.Own.o8_4278990070_10430332395
import Sqpack.S11Opt.Own.o9_6595836598_9341682191
import Sqpack.S11Opt.Own.o9_6606548751_9393532911
import Sqpack.S11Opt.Own.o9_6633137067_9363690823
import Sqpack.S11Opt.Own.o9_6652302694_9429194041
import Sqpack.S11Opt.Own.o9_6654225433_9300145690
import Sqpack.S11Opt.Own.o9_6654611924_9342215966
import Sqpack.S11Opt.Own.o9_6654611924_9363690823
import Sqpack.S11Opt.Own.o9_6676086781_9363690823
import Sqpack.S11Opt.Own.o9_6743329455_9363145060
import Sqpack.S11Opt.Own.o10_9857879057_10656374536
import Sqpack.S11Opt.Own.o10_9896637113_10637566920
import Sqpack.S11Opt.Own.o10_9917321014_10703106058
import Sqpack.S11Opt.Own.o10_9918111970_10637566920
import Sqpack.S11Opt.Own.o11_12374463655_9521270583
import Sqpack.S11Opt.Own.o11_12374463655_9604404569
import Sqpack.S11Opt.Own.o11_12605828327_9712590908
import Sqpack.S11Opt.Own.o11_12966915372_9838628626
import Sqpack.S11Opt.Own.o11_13209114097_9556997423
import Sqpack.S11Opt.Own.o11_13230588954_9556997423
import Sqpack.S11Opt.Own.o12_3516815566_13165536311
import Sqpack.S11Opt.Own.o12_3623909424_12477079687
import Sqpack.S11Opt.Own.o12_3669005666_12374534462
import Sqpack.S11Opt.Own.o12_3808741126_13234129232
import Sqpack.S11Opt.Own.o12_4285246786_12374534462
import Sqpack.S11Opt.Own.o14_9900061672_12661590962
import Sqpack.S11Opt.Own.Data
import Sqpack.S11Opt.FieldBridge

namespace SquarePacking.S11Opt.Own

open FieldTree

lemma mem_o0_3317172372_4284871135 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 0 c) :
    ptQ G.Q (3317172372, 4284871135) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o0_3317172372_4284871135_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP0 hc)
  simp only [opt_o0_3317172372_4284871135, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o0_3444858613_3789958499 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 0 c) :
    ptQ G.Q (3444858613, 3789958499) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o0_3444858613_3789958499_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP0 hc)
  simp only [opt_o0_3444858613_3789958499, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o0_3466333470_3789958499 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 0 c) :
    ptQ G.Q (3466333470, 3789958499) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o0_3466333470_3789958499_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP0 hc)
  simp only [opt_o0_3466333470_3789958499, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o0_4277969138_3746952623 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 0 c) :
    ptQ G.Q (4277969138, 3746952623) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o0_4277969138_3746952623_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP0 hc)
  simp only [opt_o0_4277969138_3746952623, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o0_4277969138_4284871135 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 0 c) :
    ptQ G.Q (4277969138, 4284871135) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o0_4277969138_4284871135_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP0 hc)
  simp only [opt_o0_4277969138_4284871135, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o1_6751901432_3990372141 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 1 c) :
    ptQ G.Q (6751901432, 3990372141) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o1_6751901432_3990372141_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP1 hc)
  simp only [opt_o1_6751901432_3990372141, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o1_6759139717_2709765890 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 1 c) :
    ptQ G.Q (6759139717, 2709765890) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o1_6759139717_2709765890_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP1 hc)
  simp only [opt_o1_6759139717_2709765890, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o1_6887576451_2748363060 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 1 c) :
    ptQ G.Q (6887576451, 2748363060) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o1_6887576451_2748363060_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP1 hc)
  simp only [opt_o1_6887576451_2748363060, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o2_9614869580_4286313812 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 2 c) :
    ptQ G.Q (9614869580, 4286313812) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o2_9614869580_4286313812_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP2 hc)
  simp only [opt_o2_9614869580_4286313812, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o2_9643989460_4178888280 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 2 c) :
    ptQ G.Q (9643989460, 4178888280) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o2_9643989460_4178888280_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP2 hc)
  simp only [opt_o2_9643989460_4178888280, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o2_9729412683_3997255438 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 2 c) :
    ptQ G.Q (9729412683, 3997255438) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o2_9729412683_3997255438_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP2 hc)
  simp only [opt_o2_9729412683_3997255438, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o2_9976778687_3798547165 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 2 c) :
    ptQ G.Q (9976778687, 3798547165) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o2_9976778687_3798547165_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP2 hc)
  simp only [opt_o2_9976778687_3798547165, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o2_9977141320_3862092438 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 2 c) :
    ptQ G.Q (9977141320, 3862092438) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o2_9977141320_3862092438_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP2 hc)
  simp only [opt_o2_9977141320_3862092438, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o3_12366716317_3090563892 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 3 c) :
    ptQ G.Q (12366716317, 3090563892) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o3_12366716317_3090563892_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP3 hc)
  simp only [opt_o3_12366716317_3090563892, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o3_12366716317_4277428641 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 3 c) :
    ptQ G.Q (12366716317, 4277428641) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o3_12366716317_4277428641_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP3 hc)
  simp only [opt_o3_12366716317_4277428641, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o3_12843221977_3417833872 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 3 c) :
    ptQ G.Q (12843221977, 3417833872) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o3_12843221977_3417833872_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP3 hc)
  simp only [opt_o3_12843221977_3417833872, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o3_12982957438_4277428641 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 3 c) :
    ptQ G.Q (12982957438, 4277428641) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o3_12982957438_4277428641_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP3 hc)
  simp only [opt_o3_12982957438_4277428641, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o3_13028053680_4174883416 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 3 c) :
    ptQ G.Q (13028053680, 4174883416) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o3_13028053680_4174883416_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP3 hc)
  simp only [opt_o3_13028053680_4174883416, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o4_3421374150_7094965680 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 4 c) :
    ptQ G.Q (3421374150, 7094965680) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o4_3421374150_7094965680_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP4 hc)
  simp only [opt_o4_3421374150_7094965680, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o4_3442849007_7094965680 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 4 c) :
    ptQ G.Q (3442849007, 7094965680) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o4_3442849007_7094965680_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP4 hc)
  simp only [opt_o4_3442849007_7094965680, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o4_3728252507_7355438087 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 4 c) :
    ptQ G.Q (3728252507, 7355438087) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o4_3728252507_7355438087_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP4 hc)
  simp only [opt_o4_3728252507_7355438087, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o4_4277499448_7047558535 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 4 c) :
    ptQ G.Q (4277499448, 7047558535) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o4_4277499448_7047558535_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP4 hc)
  simp only [opt_o4_4277499448_7047558535, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o4_4277499448_7130692521 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 4 c) :
    ptQ G.Q (4277499448, 7130692521) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o4_4277499448_7130692521_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP4 hc)
  simp only [opt_o4_4277499448_7130692521, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o5_6733851133_6014396183 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 5 c) :
    ptQ G.Q (6733851133, 6014396183) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o5_6733851133_6014396183_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP5 hc)
  simp only [opt_o5_6733851133_6014396183, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o5_6734642089_5948857046 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 5 c) :
    ptQ G.Q (6734642089, 5948857046) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o5_6734642089_5948857046_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP5 hc)
  simp only [opt_o5_6734642089_5948857046, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o8_3476074262_10265546617 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 8 c) :
    ptQ G.Q (3476074262, 10265546617) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o8_3476074262_10265546617_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP8 hc)
  simp only [opt_o8_3476074262_10265546617, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o8_3495905346_10358385407 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 8 c) :
    ptQ G.Q (3495905346, 10358385407) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o8_3495905346_10358385407_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP8 hc)
  simp only [opt_o8_3495905346_10358385407, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o8_3561497485_10083913776 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 8 c) :
    ptQ G.Q (3561497485, 10083913776) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o8_3561497485_10083913776_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP8 hc)
  simp only [opt_o8_3561497485_10083913776, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o8_3686124094_9976131924 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 8 c) :
    ptQ G.Q (3686124094, 9976131924) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o8_3686124094_9976131924_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP8 hc)
  simp only [opt_o8_3686124094_9976131924, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o8_4278990070_10189603028 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 8 c) :
    ptQ G.Q (4278990070, 10189603028) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o8_4278990070_10189603028_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP8 hc)
  simp only [opt_o8_4278990070_10189603028, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o8_4278990070_10430332395 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 8 c) :
    ptQ G.Q (4278990070, 10430332395) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o8_4278990070_10430332395_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP8 hc)
  simp only [opt_o8_4278990070_10430332395, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6595836598_9341682191 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6595836598, 9341682191) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6595836598_9341682191_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6595836598_9341682191, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6606548751_9393532911 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6606548751, 9393532911) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6606548751_9393532911_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6606548751_9393532911, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6633137067_9363690823 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6633137067, 9363690823) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6633137067_9363690823_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6633137067_9363690823, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6652302694_9429194041 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6652302694, 9429194041) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6652302694_9429194041_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6652302694_9429194041, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6654225433_9300145690 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6654225433, 9300145690) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6654225433_9300145690_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6654225433_9300145690, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6654611924_9342215966 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6654611924, 9342215966) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6654611924_9342215966_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6654611924_9342215966, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6654611924_9363690823 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6654611924, 9363690823) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6654611924_9363690823_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6654611924_9363690823, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6676086781_9363690823 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6676086781, 9363690823) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6676086781_9363690823_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6676086781_9363690823, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o9_6743329455_9363145060 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    ptQ G.Q (6743329455, 9363145060) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o9_6743329455_9363145060_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opt_o9_6743329455_9363145060, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o10_9857879057_10656374536 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 10 c) :
    ptQ G.Q (9857879057, 10656374536) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o10_9857879057_10656374536_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP10 hc)
  simp only [opt_o10_9857879057_10656374536, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o10_9896637113_10637566920 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 10 c) :
    ptQ G.Q (9896637113, 10637566920) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o10_9896637113_10637566920_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP10 hc)
  simp only [opt_o10_9896637113_10637566920, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o10_9917321014_10703106058 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 10 c) :
    ptQ G.Q (9917321014, 10703106058) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o10_9917321014_10703106058_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP10 hc)
  simp only [opt_o10_9917321014_10703106058, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o10_9918111970_10637566920 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 10 c) :
    ptQ G.Q (9918111970, 10637566920) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o10_9918111970_10637566920_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP10 hc)
  simp only [opt_o10_9918111970_10637566920, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o11_12374463655_9521270583 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 11 c) :
    ptQ G.Q (12374463655, 9521270583) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o11_12374463655_9521270583_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP11 hc)
  simp only [opt_o11_12374463655_9521270583, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o11_12374463655_9604404569 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 11 c) :
    ptQ G.Q (12374463655, 9604404569) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o11_12374463655_9604404569_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP11 hc)
  simp only [opt_o11_12374463655_9604404569, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o11_12605828327_9712590908 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 11 c) :
    ptQ G.Q (12605828327, 9712590908) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o11_12605828327_9712590908_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP11 hc)
  simp only [opt_o11_12605828327_9712590908, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o11_12966915372_9838628626 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 11 c) :
    ptQ G.Q (12966915372, 9838628626) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o11_12966915372_9838628626_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP11 hc)
  simp only [opt_o11_12966915372_9838628626, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o11_13209114097_9556997423 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 11 c) :
    ptQ G.Q (13209114097, 9556997423) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o11_13209114097_9556997423_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP11 hc)
  simp only [opt_o11_13209114097_9556997423, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o11_13230588954_9556997423 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 11 c) :
    ptQ G.Q (13230588954, 9556997423) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o11_13230588954_9556997423_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP11 hc)
  simp only [opt_o11_13230588954_9556997423, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o12_3516815566_13165536311 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 12 c) :
    ptQ G.Q (3516815566, 13165536311) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o12_3516815566_13165536311_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP12 hc)
  simp only [opt_o12_3516815566_13165536311, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o12_3623909424_12477079687 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 12 c) :
    ptQ G.Q (3623909424, 12477079687) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o12_3623909424_12477079687_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP12 hc)
  simp only [opt_o12_3623909424_12477079687, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o12_3669005666_12374534462 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 12 c) :
    ptQ G.Q (3669005666, 12374534462) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o12_3669005666_12374534462_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP12 hc)
  simp only [opt_o12_3669005666_12374534462, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o12_3808741126_13234129232 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 12 c) :
    ptQ G.Q (3808741126, 13234129232) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o12_3808741126_13234129232_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP12 hc)
  simp only [opt_o12_3808741126_13234129232, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o12_4285246786_12374534462 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 12 c) :
    ptQ G.Q (4285246786, 12374534462) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o12_4285246786_12374534462_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP12 hc)
  simp only [opt_o12_4285246786_12374534462, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

lemma mem_o14_9900061672_12661590962 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 14 c) :
    ptQ G.Q (9900061672, 12661590962) ∈ ScSq G.sc c θ := by
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_o14_9900061672_12661590962_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP14 hc)
  simp only [opt_o14_9900061672_12661590962, List.mem_singleton] at hop
  subst hop
  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hp'
  subst hp'
  exact hm

theorem reg_mem : ∀ e ∈ reg, ∀ {c : ℝ × ℝ} {θ : ℝ}, sq c θ 1 ⊆ box Ux → InCellU e.1 c →
    ptQ G.Q e.2 ∈ ScSq G.sc c θ := by
  intro e he
  simp only [reg, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun hin hc => mem_o0_3317172372_4284871135 hin hc
  · exact fun hin hc => mem_o0_3444858613_3789958499 hin hc
  · exact fun hin hc => mem_o0_3466333470_3789958499 hin hc
  · exact fun hin hc => mem_o0_4277969138_3746952623 hin hc
  · exact fun hin hc => mem_o0_4277969138_4284871135 hin hc
  · exact fun hin hc => mem_o1_6751901432_3990372141 hin hc
  · exact fun hin hc => mem_o1_6759139717_2709765890 hin hc
  · exact fun hin hc => mem_o1_6887576451_2748363060 hin hc
  · exact fun hin hc => mem_o2_9614869580_4286313812 hin hc
  · exact fun hin hc => mem_o2_9643989460_4178888280 hin hc
  · exact fun hin hc => mem_o2_9729412683_3997255438 hin hc
  · exact fun hin hc => mem_o2_9976778687_3798547165 hin hc
  · exact fun hin hc => mem_o2_9977141320_3862092438 hin hc
  · exact fun hin hc => mem_o3_12366716317_3090563892 hin hc
  · exact fun hin hc => mem_o3_12366716317_4277428641 hin hc
  · exact fun hin hc => mem_o3_12843221977_3417833872 hin hc
  · exact fun hin hc => mem_o3_12982957438_4277428641 hin hc
  · exact fun hin hc => mem_o3_13028053680_4174883416 hin hc
  · exact fun hin hc => mem_o4_3421374150_7094965680 hin hc
  · exact fun hin hc => mem_o4_3442849007_7094965680 hin hc
  · exact fun hin hc => mem_o4_3728252507_7355438087 hin hc
  · exact fun hin hc => mem_o4_4277499448_7047558535 hin hc
  · exact fun hin hc => mem_o4_4277499448_7130692521 hin hc
  · exact fun hin hc => mem_o5_6733851133_6014396183 hin hc
  · exact fun hin hc => mem_o5_6734642089_5948857046 hin hc
  · exact fun hin hc => mem_o8_3476074262_10265546617 hin hc
  · exact fun hin hc => mem_o8_3495905346_10358385407 hin hc
  · exact fun hin hc => mem_o8_3561497485_10083913776 hin hc
  · exact fun hin hc => mem_o8_3686124094_9976131924 hin hc
  · exact fun hin hc => mem_o8_4278990070_10189603028 hin hc
  · exact fun hin hc => mem_o8_4278990070_10430332395 hin hc
  · exact fun hin hc => mem_o9_6595836598_9341682191 hin hc
  · exact fun hin hc => mem_o9_6606548751_9393532911 hin hc
  · exact fun hin hc => mem_o9_6633137067_9363690823 hin hc
  · exact fun hin hc => mem_o9_6652302694_9429194041 hin hc
  · exact fun hin hc => mem_o9_6654225433_9300145690 hin hc
  · exact fun hin hc => mem_o9_6654611924_9342215966 hin hc
  · exact fun hin hc => mem_o9_6654611924_9363690823 hin hc
  · exact fun hin hc => mem_o9_6676086781_9363690823 hin hc
  · exact fun hin hc => mem_o9_6743329455_9363145060 hin hc
  · exact fun hin hc => mem_o10_9857879057_10656374536 hin hc
  · exact fun hin hc => mem_o10_9896637113_10637566920 hin hc
  · exact fun hin hc => mem_o10_9917321014_10703106058 hin hc
  · exact fun hin hc => mem_o10_9918111970_10637566920 hin hc
  · exact fun hin hc => mem_o11_12374463655_9521270583 hin hc
  · exact fun hin hc => mem_o11_12374463655_9604404569 hin hc
  · exact fun hin hc => mem_o11_12605828327_9712590908 hin hc
  · exact fun hin hc => mem_o11_12966915372_9838628626 hin hc
  · exact fun hin hc => mem_o11_13209114097_9556997423 hin hc
  · exact fun hin hc => mem_o11_13230588954_9556997423 hin hc
  · exact fun hin hc => mem_o12_3516815566_13165536311 hin hc
  · exact fun hin hc => mem_o12_3623909424_12477079687 hin hc
  · exact fun hin hc => mem_o12_3669005666_12374534462 hin hc
  · exact fun hin hc => mem_o12_3808741126_13234129232 hin hc
  · exact fun hin hc => mem_o12_4285246786_12374534462 hin hc
  · exact fun hin hc => mem_o14_9900061672_12661590962 hin hc

end SquarePacking.S11Opt.Own
