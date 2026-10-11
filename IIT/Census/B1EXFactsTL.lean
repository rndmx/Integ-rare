/-
Census, B1 lower bound part (b): checks T and L of `EXFacts` hold on `E_X` w.h.p.

Cell averages of `-log y` (pair cells; strip averages) and of `-log x_s` (row-`s` cells; interval averages of
`-log x` on the upper interval) are bounded by the kernel-checked values of `CertEXAvg`, then `EX_pair_dev` /
`EX_s_dev` give the deviation bounds.
-/
import IIT.Census.B1EXDev
import IIT.Census.CertEXAvg

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory Filter Finset

variable {N : ℕ}

/-! ### Integrals over cells -/

lemma unif_setIntegral_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (h : ℝ → ℝ) :
    ∫ y in Set.Ico a b, h y ∂unif = ∫ y in a..b, h y := by
  unfold unif
  rw [Measure.restrict_restrict measurableSet_Ico,
    Set.inter_eq_left.2 (Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb)),
    integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- `∫_a^b -log y = -(b log b - a log a - b + a)`. -/
lemma integral_neg_log (a b : ℝ) : ∫ y in a..b, -Real.log y = -(b * Real.log b - a * Real.log a - b + a) := by
  rw [intervalIntegral.integral_neg, integral_log]

lemma exYlo_ge (C : EXPCell) : (exF : ℝ) ≤ exYlo C := by
  have : exF ≤ exYlo C := by
    unfold exYlo; have := exHy_pos
    have : (0 : ℚ) ≤ C.sa * exHy := by positivity
    linarith
  exact_mod_cast this

/-- The `T`-function. -/
noncomputable def gT (p : ℝ × ℝ) : ℝ := -Real.log (clamp01 p.1)

lemma measurable_gT : Measurable gT :=
  (Real.measurable_log.comp (clamp01_measurable.comp measurable_fst)).neg

lemma exYhi_le (C : EXPCell) (hC : C ∈ exPCells) : ((exYlo C + exHy : ℚ) : ℝ) ≤ 1 := by
  obtain ⟨-, hsa, -⟩ := exP_facts hC
  have : exYlo C + exHy ≤ 1 := by
    unfold exYlo exF; rw [exHy_val]
    have : (C.sa : ℚ) ≤ 39 := by exact_mod_cast Nat.lt_succ_iff.1 hsa
    linarith
  exact_mod_cast this

lemma exF_pos : (0 : ℝ) < exF := by unfold exF; norm_num

/-- **Strip average**: the pair-cell average of `gT` is the strip average of `-log y`. -/
lemma avg_gT (C : EXPCell) (hC : C ∈ exPCells) :
    (∫ p in exIP C, gT p ∂(unif.prod unif)) / ((exHy : ℝ) * (C.u1 - C.u0)) =
      -(((exYlo C + exHy : ℚ) : ℝ) * Real.log ((exYlo C + exHy : ℚ) : ℝ) -
          (exYlo C : ℝ) * Real.log (exYlo C : ℝ) - ((exYlo C + exHy : ℚ) : ℝ) + exYlo C) / exHy := by
  obtain ⟨-, -, hu0, hu01, hu1, -⟩ := exP_facts hC
  have hy0 : (0 : ℝ) ≤ exYlo C := exF_pos.le.trans (exYlo_ge C)
  have hyy : (exYlo C : ℝ) ≤ ((exYlo C + exHy : ℚ) : ℝ) := by
    have := exHy_pos; exact_mod_cast (by linarith : exYlo C ≤ exYlo C + exHy)
  have hy1 := exYhi_le C hC
  have hhy : (0 : ℝ) < exHy := by exact_mod_cast exHy_pos
  have hu : (0 : ℝ) < (C.u1 : ℝ) - C.u0 := by have : (C.u0 : ℝ) < C.u1 := by exact_mod_cast hu01
                                              linarith
  have hprod : ∫ p in exIP C, gT p ∂(unif.prod unif) =
      (∫ y in Set.Ico (exYlo C : ℝ) ((exYlo C + exHy : ℚ) : ℝ), -Real.log (clamp01 y) ∂unif) *
        ∫ _u in Set.Ico (C.u0 : ℝ) C.u1, (1 : ℝ) ∂unif := by
    rw [exIP, ← setIntegral_prod_mul]; simp [gT]
  rw [hprod, unif_setIntegral_Ico hy0 hyy hy1, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    unif_Ico (by exact_mod_cast hu0) (by exact_mod_cast hu01.le) (by exact_mod_cast hu1),
    ENNReal.toReal_ofReal hu.le]
  have hcl : ∫ y in (exYlo C : ℝ)..((exYlo C + exHy : ℚ) : ℝ), -Real.log (clamp01 y) =
      ∫ y in (exYlo C : ℝ)..((exYlo C + exHy : ℚ) : ℝ), -Real.log y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hyy] at hy
    have : clamp01 y = y := by
      unfold clamp01; rw [min_eq_right (hy.2.trans hy1), max_eq_right (hy0.trans hy.1)]
    simp only [this]
  rw [hcl, integral_neg_log]
  have hyhi : ((exYlo C + exHy : ℚ) : ℝ) - exYlo C = exHy := by push_cast; ring
  field_simp

/-- Log bounds at a listed point. -/
lemma exPt_log {p : ℚ × ℤ × ℚ × ℚ} (h : exPtOK p = true) :
    (p.2.2.1 : ℝ) ≤ Real.log p.1 ∧ Real.log p.1 ≤ p.2.2.2 := by
  simp only [exPtOK, Bool.and_eq_true] at h
  exact ⟨crLog_ge p.2.1 40 (by simpa only [Bool.and_eq_true] using h.1),
    crLog_le p.2.1 40 (by simpa only [Bool.and_eq_true] using h.2)⟩

lemma exYp_ok {sa : ℕ} (h : sa < 41) : exPtOK (exYp sa) = true := by
  have hl : sa < exYpts.length := by rw [exYpts_len]; exact h
  unfold exYp; rw [List.getD_eq_getElem _ _ hl]
  exact (List.all_eq_true.1 exYpts_ok) _ (List.getElem_mem hl)

lemma exXp_ok {j : ℕ} (h : j < 201) : exPtOK (exXp j) = true := by
  have hl : j < exXpts.length := by rw [exXpts_len]; exact h
  unfold exXp; rw [List.getD_eq_getElem _ _ hl]
  exact (List.all_eq_true.1 exXpts_ok) _ (List.getElem_mem hl)

lemma exYp_val {sa : ℕ} (h : sa < 41) : (exYp sa).1 = exF + sa * exHy := by
  have := (List.all_eq_true.1 exYpts_val) sa (List.mem_range.2 h)
  simpa using this

/-- **Bounds of the `T`-average of a pair cell.** -/
lemma avg_gT_bounds (i : Fin KP) :
    ((exBTlo (cP i).sa : ℚ) : ℝ) ≤ (∫ p in exIP (cP i), gT p ∂(unif.prod unif)) / ellP i ∧
      (∫ p in exIP (cP i), gT p ∂(unif.prod unif)) / ellP i ≤ ((exBTup (cP i).sa : ℚ) : ℝ) := by
  set C := cP i
  have hC : C ∈ exPCells := cP_mem i
  have hsa : C.sa < 40 := (exP_facts hC).2.1
  rw [show ellP i = (exHy : ℝ) * (C.u1 - C.u0) from rfl, avg_gT C hC]
  have h0 := exPt_log (exYp_ok (sa := C.sa) (by omega))
  have h1 := exPt_log (exYp_ok (sa := C.sa + 1) (by omega))
  have v0 : (exYp C.sa).1 = exYlo C := by rw [exYp_val (by omega)]; rfl
  have v1 : (exYp (C.sa + 1)).1 = exYlo C + exHy := by rw [exYp_val (by omega)]; unfold exYlo; push_cast; ring
  rw [v0] at h0; rw [v1] at h1
  have hy0 : (0 : ℝ) ≤ exYlo C := exF_pos.le.trans (exYlo_ge C)
  have hy1 : (0 : ℝ) ≤ ((exYlo C + exHy : ℚ) : ℝ) := by
    have := exHy_pos; have : (0 : ℝ) ≤ exHy := by exact_mod_cast this.le
    push_cast; linarith
  have hhy : (0 : ℝ) < exHy := by exact_mod_cast exHy_pos
  unfold exBTup exBTlo
  rw [v0, v1]
  push_cast at h0 h1 hy1 ⊢
  constructor
  · rw [div_le_div_iff_of_pos_right hhy]
    nlinarith [mul_le_mul_of_nonneg_left h1.2 hy1, mul_le_mul_of_nonneg_left h0.1 hy0]
  · rw [div_le_div_iff_of_pos_right hhy]
    nlinarith [mul_le_mul_of_nonneg_left h1.1 hy1, mul_le_mul_of_nonneg_left h0.2 hy0]

/-- The `L`-function: `-log x_k`, `x_k = max(y, 1 - y)`. -/
noncomputable def gL (v : ℝ) : ℝ := -Real.log (max (clamp01 v) (1 - clamp01 v))

lemma measurable_gL : Measurable gL :=
  (Real.measurable_log.comp (clamp01_measurable.max (measurable_const.sub clamp01_measurable))).neg

lemma exXp_range {j : ℕ} (h : j < 201) : (1 / 2 : ℝ) < (exXp j).1 ∧ ((exXp j).1 : ℝ) ≤ 1 := by
  have := (List.all_eq_true.1 exXpts_range) j (List.mem_range.2 h)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  have h1 := (Rat.cast_lt (K := ℝ)).2 this.1
  have h2 := (Rat.cast_le (K := ℝ)).2 this.2
  push_cast at h1 h2
  exact ⟨h1, h2⟩

lemma exXp_lt {j : ℕ} (h : j < 200) : ((exXp j).1 : ℝ) < (exXp (j + 1)).1 := by
  have := (List.all_eq_true.1 exXpts_inc) j (List.mem_range.2 h)
  exact_mod_cast of_decide_eq_true this

/-- **Bound of the `L`-average of a row-`s` cell** through its upper interval `[x_j, x_{j+1}]`. -/
lemma avg_gL_le (C : EXSCell) (j : ℕ) (hj : exSIdxOK C j = true) :
    (∫ v in exIS C, gL v ∂unif) / ((C.x1 : ℝ) - C.x0) ≤ ((exBLup j : ℚ) : ℝ) := by
  simp only [exSIdxOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hj
  obtain ⟨hj2, hcase⟩ := hj
  set a : ℝ := ((exXp j).1 : ℝ) with ha
  set b : ℝ := ((exXp (j + 1)).1 : ℝ) with hb
  obtain ⟨ha1, ha2⟩ := exXp_range (j := j) (by omega)
  obtain ⟨hb1, hb2⟩ := exXp_range (j := j + 1) (by omega)
  have hab : a < b := exXp_lt hj2
  have hint : (∫ v in exIS C, gL v ∂unif) = ∫ x in a..b, -Real.log x := by
    rcases hcase with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have e0 : (C.x0 : ℝ) = a := by rw [h0]
      have e1 : (C.x1 : ℝ) = b := by rw [h1]
      rw [exIS, e0, e1, unif_setIntegral_Ico (by linarith) hab.le hb2]
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le hab.le] at hy
      have hc : clamp01 y = y := by
        unfold clamp01; rw [min_eq_right (hy.2.trans hb2), max_eq_right (by linarith [hy.1])]
      simp only [gL, hc]; rw [max_eq_left (by linarith [hy.1])]
    · have e0 : (C.x0 : ℝ) = 1 - b := by rw [h0]; push_cast; rfl
      have e1 : (C.x1 : ℝ) = 1 - a := by rw [h1]; push_cast; rfl
      rw [exIS, e0, e1, unif_setIntegral_Ico (by linarith) (by linarith) (by linarith)]
      have : ∫ v in (1 - b)..(1 - a), gL v = ∫ v in (1 - b)..(1 - a), -Real.log (1 - v) := by
        refine intervalIntegral.integral_congr fun y hy => ?_
        rw [Set.uIcc_of_le (by linarith)] at hy
        have hc : clamp01 y = y := by
          unfold clamp01; rw [min_eq_right (by linarith [hy.2]), max_eq_right (by linarith [hy.1])]
        simp only [gL, hc]; rw [max_eq_right (by linarith [hy.2])]
      rw [this, intervalIntegral.integral_comp_sub_left (fun x => -Real.log x) 1]
      simp
  have hlen : (C.x1 : ℝ) - C.x0 = b - a := by
    rcases hcase with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1]
    · rw [h0, h1]; push_cast; ring
  rw [hint, hlen, integral_neg_log]
  have l0 := exPt_log (exXp_ok (j := j) (by omega))
  have l1 := exPt_log (exXp_ok (j := j + 1) (by omega))
  unfold exBLup
  push_cast
  rw [← ha, ← hb] at *
  have hba : 0 < b - a := by linarith
  rw [div_le_div_iff_of_pos_right hba]
  nlinarith [mul_le_mul_of_nonneg_left l1.1 (by linarith : (0 : ℝ) ≤ b),
    mul_le_mul_of_nonneg_left l0.2 (by linarith : (0 : ℝ) ≤ a)]

/-- `c log N ≤ ε N` eventually. -/
lemma ev_log_le (c ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, c * Real.log N ≤ ε * N := by
  have hlo := Real.isLittleO_log_id_atTop
  have h1 := hlo.def (c := ε / (|c| + 1)) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h1, eventually_ge_atTop 1] with N hN hN1
  simp only [Real.norm_eq_abs, id] at hN
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [abs_of_nonneg hl, abs_of_nonneg hN0] at hN
  have hc : c * Real.log N ≤ |c| * Real.log N := mul_le_mul_of_nonneg_right (le_abs_self c) hl
  have : |c| * Real.log N ≤ |c| * (ε / (|c| + 1) * N) := mul_le_mul_of_nonneg_left hN (abs_nonneg c)
  have h2 : |c| * (ε / (|c| + 1) * N) ≤ ε * N := by
    rw [← mul_assoc, mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg c, mul_nonneg hε.le hN0]
  linarith

lemma sum_T_up : ∑ i : Fin KP, ((cP i).a : ℝ) * ((exBTup (cP i).sa : ℚ) : ℝ) ≤ exETup := by
  have h := Fin.sum_univ_fun_getElem exPCells (fun C : EXPCell => (C.a : ℝ) * ((exBTup C.sa : ℚ) : ℝ))
  simp only [cP]
  rw [h]
  have e : (((exPCells.map fun C => C.a * exBTup C.sa).sum : ℚ) : ℝ) =
      (exPCells.map fun C => (C.a : ℝ) * ((exBTup C.sa : ℚ) : ℝ)).sum := by
    rw [Rat.cast_list_sum, List.map_map]; congr 1; exact List.map_congr_left fun C _ => Rat.cast_mul _ _
  rw [← e]; exact (Rat.cast_le (K := ℝ)).2 exT_up

lemma sum_T_lo : (exETlo : ℝ) ≤ ∑ i : Fin KP, ((cP i).a : ℝ) * ((exBTlo (cP i).sa : ℚ) : ℝ) := by
  have h := Fin.sum_univ_fun_getElem exPCells (fun C : EXPCell => (C.a : ℝ) * ((exBTlo C.sa : ℚ) : ℝ))
  simp only [cP]
  rw [h]
  have e : (((exPCells.map fun C => C.a * exBTlo C.sa).sum : ℚ) : ℝ) =
      (exPCells.map fun C => (C.a : ℝ) * ((exBTlo C.sa : ℚ) : ℝ)).sum := by
    rw [Rat.cast_list_sum, List.map_map]; congr 1; exact List.map_congr_left fun C _ => Rat.cast_mul _ _
  rw [← e]; exact (Rat.cast_le (K := ℝ)).2 exT_lo

lemma gT_range (i : Fin KP) : ∀ p ∈ exIP (cP i), gT p ∈ Set.Icc (0 : ℝ) 1 := by
  intro p hp
  have hy0 := exYlo_ge (cP i)
  have hy1 := exYhi_le (cP i) (cP_mem i)
  obtain ⟨⟨h1, h2⟩, -⟩ := hp
  have hpos : (0 : ℝ) < p.1 := lt_of_lt_of_le exF_pos (hy0.trans h1)
  have hle : p.1 ≤ 1 := (le_of_lt h2).trans hy1
  have hc : clamp01 p.1 = p.1 := by unfold clamp01; rw [min_eq_right hle, max_eq_right hpos.le]
  simp only [gT, hc]
  constructor
  · have := Real.log_nonpos hpos.le hle; linarith
  · have hf : (1001 / 2000 : ℝ) ≤ p.1 := by
      have : ((exF : ℚ) : ℝ) = 1001 / 2000 := by unfold exF; norm_num
      linarith [hy0.trans h1]
    have := Real.add_one_le_exp (-1)
    have hl : -1 ≤ Real.log p.1 := by
      rw [Real.le_log_iff_exp_le hpos]
      have : Real.exp (-1) ≤ 1001 / 2000 := by
        have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
      linarith
    linarith

/-- **Check T fails rarely on `E_X`.** -/
theorem EX_T_fail : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
    cubeM N (EX N s r0 x ∩ {w | ¬ XW w r0 ≤ x0 * N - 9 * Real.log N}) ≤
      cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (1 / (8 * 10 ^ 6)) ^ 2 / (1 - 0) ^ 2))) := by
  have hdev := EX_pair_dev gT measurable_gT (a := 0) (b := 1) one_pos gT_range
    (fun i => ((exBTup (cP i).sa : ℚ) : ℝ)) (fun i => (avg_gT_bounds i).2) sum_T_up
    (η := 1 / (4 * 10 ^ 6)) (by norm_num)
  have hm := (Rat.cast_lt (K := ℝ)).2 exT_margin
  push_cast at hm
  have hx0 := cr_x0_bounds.1
  filter_upwards [hdev, ev_log_le 9 (1 / (4 * 10 ^ 6)) (by norm_num)] with N hN hlog s r0 x h0 h1
  have he : (1 / (4 * 10 ^ 6) / 2 : ℝ) = 1 / (8 * 10 ^ 6) := by norm_num
  rw [he] at hN
  refine le_trans (measure_mono (s := EX N s r0 x ∩ {w | ¬ XW w r0 ≤ x0 * N - 9 * Real.log N})
    (t := EX N s r0 x ∩ {w | N * (exETup + 1 / (4 * 10 ^ 6)) ≤ ∑ j, gT (w r0 j, w (flipAt x r0) j)}) ?_)
    (hN s r0 x h0 h1)
  rintro w ⟨hw, hT⟩
  refine ⟨hw, ?_⟩
  simp only [Set.mem_setOf_eq, not_le] at hT ⊢
  have hX : XW w r0 = ∑ j, gT (w r0 j, w (flipAt x r0) j) := by simp [XW, gT]
  rw [← hX]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

lemma exZip_len : (exSCells.zip exSIdx).length = KS := by
  rw [List.length_zip, exSIdx_len]; simp [KS, exSCells_len]

/-- The upper-interval index of row-`s` cell `i`. -/
def sIdx (i : Fin KS) : ℕ := exSIdx.getD i.1 0

lemma sIdx_ok (i : Fin KS) : exSIdxOK (cS i) (sIdx i) = true := by
  have hi : i.1 < (exSCells.zip exSIdx).length := by rw [exZip_len]; exact i.2
  have hm := (List.all_eq_true.1 exSIdx_ok) _ (List.getElem_mem hi)
  rw [List.getElem_zip] at hm
  have hi2 : i.1 < exSIdx.length := by rw [exSIdx_len]; have := i.2; simp only [KS, exSCells_len] at this; exact this
  unfold sIdx cS; rw [List.getD_eq_getElem _ _ hi2]; exact hm

lemma sum_L_up : ∑ i : Fin KS, ((cS i).a : ℝ) * ((exBLup (sIdx i) : ℚ) : ℝ) ≤ exELup := by
  set Z := exSCells.zip exSIdx
  have hrec : ∀ i : Fin KS, ((cS i).a : ℝ) * ((exBLup (sIdx i) : ℚ) : ℝ) =
      (fun p : EXSCell × ℕ => (p.1.a : ℝ) * ((exBLup p.2 : ℚ) : ℝ)) (Z[i.1]'(by rw [exZip_len]; exact i.2)) := by
    intro i
    have hi2 : i.1 < exSIdx.length := by rw [exSIdx_len]; have := i.2; simp only [KS, exSCells_len] at this; exact this
    simp only [Z, List.getElem_zip, cS, sIdx, List.getD_eq_getElem _ _ hi2]
  rw [Finset.sum_congr rfl fun i _ => hrec i]
  set F := fun p : EXSCell × ℕ => (p.1.a : ℝ) * ((exBLup p.2 : ℚ) : ℝ) with hF
  refine le_of_eq_of_le (Fintype.sum_equiv (finCongr exZip_len.symm) _ (fun j : Fin Z.length => F Z[j.1])
    (fun i => rfl)) ?_
  rw [Fin.sum_univ_fun_getElem Z F]
  have e : (((Z.map fun p => p.1.a * exBLup p.2).sum : ℚ) : ℝ) =
      (Z.map fun p : EXSCell × ℕ => (p.1.a : ℝ) * ((exBLup p.2 : ℚ) : ℝ)).sum := by
    rw [Rat.cast_list_sum, List.map_map]; congr 1; exact List.map_congr_left fun p _ => Rat.cast_mul _ _
  rw [← e]; exact (Rat.cast_le (K := ℝ)).2 exL_up

lemma gL_range (i : Fin KS) : ∀ v ∈ exIS (cS i), gL v ∈ Set.Icc (0 : ℝ) 1 := by
  intro v _
  have h0 := clamp01_nonneg v
  have h1 := clamp01_le_one v
  set m := max (clamp01 v) (1 - clamp01 v)
  have hm1 : m ≤ 1 := max_le h1 (by linarith)
  have hmh : (1 / 2 : ℝ) ≤ m := by
    rcases le_total (clamp01 v) (1 / 2) with h | h
    · exact le_trans (by linarith) (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
  have hmpos : 0 < m := by linarith
  simp only [gL]
  constructor
  · have := Real.log_nonpos hmpos.le hm1; linarith
  · have : -1 ≤ Real.log m := by
      rw [Real.le_log_iff_exp_le hmpos]
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    linarith

/-- **Check L fails rarely on `E_X`.** -/
theorem EX_L_fail : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
    cubeM N (EX N s r0 x ∩ {w | ¬ ∑ k, -Real.log (xE w s k) ≤ XW w r0 - 3 * Real.log N}) ≤
      cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (1 / (2 * 10 ^ 7)) ^ 2 / (1 - 0) ^ 2))) +
      cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (1 / (2 * 10 ^ 7)) ^ 2 / (1 - 0) ^ 2))) := by
  have hs := EX_s_dev gL measurable_gL (a := 0) (b := 1) one_pos gL_range (fun i => ((exBLup (sIdx i) : ℚ) : ℝ))
    (fun i => avg_gL_le (cS i) (sIdx i) (sIdx_ok i)) sum_L_up (η := 1 / 10 ^ 7) (by norm_num)
  have hp := EX_pair_dev_lo gT measurable_gT (a := 0) (b := 1) one_pos gT_range
    (fun i => ((exBTlo (cP i).sa : ℚ) : ℝ)) (fun i => (avg_gT_bounds i).1) sum_T_lo
    (η := 1 / 10 ^ 7) (by norm_num)
  have hm := (Rat.cast_lt (K := ℝ)).2 exL_margin
  push_cast at hm
  filter_upwards [hs, hp, ev_log_le 3 (1 / (5 * 10 ^ 6)) (by norm_num)] with N hN1 hN2 hlog s r0 x h0 h1
  have he : (1 / 10 ^ 7 / 2 : ℝ) = 1 / (2 * 10 ^ 7) := by norm_num
  rw [he] at hN1 hN2
  refine le_trans (measure_mono (s := EX N s r0 x ∩ {w | ¬ ∑ k, -Real.log (xE w s k) ≤ XW w r0 - 3 * Real.log N})
    (t := (EX N s r0 x ∩ {w | N * (exELup + 1 / 10 ^ 7) ≤ ∑ k, gL (w s k)}) ∪
      (EX N s r0 x ∩ {w | ∑ j, gT (w r0 j, w (flipAt x r0) j) ≤ N * (exETlo - 1 / 10 ^ 7)})) ?_)
    ((measure_union_le _ _).trans (add_le_add (hN1 s r0 x h0 h1) (hN2 s r0 x h0 h1)))
  rintro w ⟨hw, hL⟩
  have hX : XW w r0 = ∑ j, gT (w r0 j, w (flipAt x r0) j) := by simp [XW, gT]
  have hS : ∑ k, -Real.log (xE w s k) = ∑ k, gL (w s k) := by simp [xE, gL]
  simp only [Set.mem_setOf_eq, not_le] at hL
  rw [hX, hS] at hL
  by_contra hno
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_or, not_and, not_le] at hno
  have a1 := hno.1 hw
  have a2 := hno.2 hw
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

end Census
end IIT
