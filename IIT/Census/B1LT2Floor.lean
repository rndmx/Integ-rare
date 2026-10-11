/-
Census, B1 lemma LT2, module M4 part 5a: the tilted mean of the heavy window.

`L(x) = Σ_j -log y_j`, `f(x) = P_ns(x)² 1{L ≤ 0.38N} = P² 1{x₁N < L ≤ 0.38N}`.
* `lt2_tilt_int`: `∫ e^{tL} = (1-t)^{-N}` (`t < 1`).
* `lt2_Ef_ge`: `E f ≥ 3^{-N} - e^{-λ₁ 0.38N}(3-λ₁)^{-N} - e^{λ₂ x₁N}(3+λ₂)^{-N}`, and `E f ≥ 3^{-N}/2` eventually
  (rates `0.38λ₁ + log((3-λ₁)/3) ≥ 0.0089` at `λ₁ = 0.37`, `log((3+λ₂)/3) - λ₂x₁ ≥ 0.1` at `λ₂ = 1.87`).
-/
import IIT.Census.B1LT2Pairs

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- `L(x) = Σ_j -log y_j`. -/
noncomputable def lt2L (x : Fin N → ℝ) : ℝ := ∑ i, -Real.log (clamp01 (x i))

lemma lt2L_nonneg (x : Fin N → ℝ) : 0 ≤ lt2L x :=
  Finset.sum_nonneg fun i _ => neg_nonneg.2 (Real.log_nonpos (clamp01_nonneg _) (clamp01_le_one _))

lemma lt2L_measurable : Measurable (lt2L (N := N)) := lt2_measurable_negLog

lemma lt2_int_unif_negLog {t : ℝ} (ht : t < 1) :
    ∫ u, Real.exp (t * -Real.log (clamp01 u)) ∂unif = 1 / (1 - t) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u => (Real.exp_pos _).le)
    (Real.measurable_exp.comp (measurable_negLogClamp.const_mul t)).aestronglyMeasurable,
    lintegral_unif_negLog ht, ENNReal.toReal_ofReal (by rw [one_div]; exact inv_nonneg.2 (by linarith))]

/-- **The tilted moment**: `∫ e^{tL} = (1-t)^{-N}`. -/
lemma lt2_tilt_int {t : ℝ} (ht : t < 1) : ∫ v, Real.exp (t * lt2L v) ∂rowM N = (1 / (1 - t)) ^ N := by
  unfold lt2L
  simp_rw [Finset.mul_sum, Real.exp_sum]
  unfold rowM
  rw [integral_fintype_prod_eq_prod (fun _ u => Real.exp (t * -Real.log (clamp01 u)))]
  simp only [lt2_int_unif_negLog ht, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma lt2_tilt_integrable {t : ℝ} (ht : t ≤ 0) : Integrable (fun v => Real.exp (t * lt2L v)) (rowM N) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  refine Integrable.of_bound (Real.measurable_exp.comp (lt2L_measurable.const_mul t)).aestronglyMeasurable 1
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg ht (lt2L_nonneg v)

lemma lt2_P_le_exp (x : Fin N → ℝ) : ∏ j, clamp01 (x j) ≤ Real.exp (-lt2L x) := by
  unfold lt2L
  by_cases hpos : ∀ j, 0 < clamp01 (x j)
  · apply le_of_eq
    rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos j)).symm
  · push_neg at hpos
    obtain ⟨j, h0⟩ := hpos
    rw [Finset.prod_eq_zero (mem_univ j) (le_antisymm h0 (clamp01_nonneg _))]
    exact (Real.exp_pos _).le

lemma lt2_P_sq_le_exp (x : Fin N → ℝ) : (∏ j, clamp01 (x j)) ^ 2 ≤ Real.exp (-2 * lt2L x) := by
  have h := lt2_P_le_exp x
  have h0 : 0 ≤ ∏ j, clamp01 (x j) := Finset.prod_nonneg fun j _ => clamp01_nonneg _
  calc (∏ j, clamp01 (x j)) ^ 2 ≤ Real.exp (-lt2L x) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = Real.exp (-2 * lt2L x) := by rw [← Real.exp_nat_mul]; ring_nf

/-- The heavy-window weight `f = P_ns² 1{L ≤ 0.38N}`. -/
noncomputable def lt2fH (x : Fin N → ℝ) : ℝ := if lt2L x ≤ 38 / 100 * (N : ℝ) then lt2gNs x ^ 2 else 0

lemma lt2fH_nonneg (x : Fin N → ℝ) : 0 ≤ lt2fH x := by unfold lt2fH; split_ifs <;> positivity

lemma lt2fH_le (x : Fin N → ℝ) : lt2fH x ≤ lt2θ N ^ 2 := by
  unfold lt2fH; split_ifs
  · exact pow_le_pow_left₀ (lt2gNs_nonneg x) (lt2gNs_le x) 2
  · positivity

lemma lt2fH_measurable : Measurable (lt2fH (N := N)) :=
  Measurable.ite (measurableSet_le lt2L_measurable measurable_const) (lt2gNs_measurable.pow_const 2) measurable_const

/-- `f = P² - P² 1{L > a} - P² 1{L ≤ x₁N}`, pointwise. -/
lemma lt2fH_eq (x : Fin N → ℝ) :
    lt2fH x = (∏ j, clamp01 (x j)) ^ 2 - (if 38 / 100 * (N : ℝ) < lt2L x then (∏ j, clamp01 (x j)) ^ 2 else 0)
      - (if lt2L x ≤ lt2x1 * N then (∏ j, clamp01 (x j)) ^ 2 else 0) := by
  have hx1 := lt2x1_bounds
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold lt2fH lt2gNs
  have hL : lt2L x = ∑ j, -Real.log (clamp01 (x j)) := rfl
  rw [← hL]
  by_cases h1 : lt2L x ≤ 38 / 100 * (N : ℝ)
  · rw [if_pos h1, if_neg (not_lt.2 h1)]
    by_cases h2 : lt2x1 * N < lt2L x
    · rw [if_pos h2, if_neg (not_le.2 h2)]; ring
    · rw [if_neg h2, if_pos (not_lt.1 h2)]; ring
  · rw [if_neg h1, if_pos (not_le.1 h1), if_neg (by nlinarith [not_le.1 h1, hx1.2])]; ring

lemma lt2_tail_hi_le {a l : ℝ} (hl : 0 ≤ l) (x : Fin N → ℝ) :
    (if a < lt2L x then (∏ j, clamp01 (x j)) ^ 2 else 0) ≤ Real.exp (-(l * a)) * Real.exp ((l - 2) * lt2L x) := by
  split_ifs with h
  · refine (lt2_P_sq_le_exp x).trans ?_
    rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
  · positivity

lemma lt2_tail_lo_le {b l : ℝ} (hl : 0 ≤ l) (x : Fin N → ℝ) :
    (if lt2L x ≤ b then (∏ j, clamp01 (x j)) ^ 2 else 0) ≤ Real.exp (l * b) * Real.exp ((-2 - l) * lt2L x) := by
  split_ifs with h
  · refine (lt2_P_sq_le_exp x).trans ?_
    rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
  · positivity

/-- **The tilted mean of the heavy window.** -/
theorem lt2_Ef_ge {l1 l2 : ℝ} (hl1 : 0 ≤ l1) (hl1' : l1 ≤ 2) (hl2 : 0 ≤ l2) :
    (1 / 3 : ℝ) ^ N - Real.exp (-(l1 * (38 / 100 * N))) * (1 / (3 - l1)) ^ N
      - Real.exp (l2 * (lt2x1 * N)) * (1 / (3 + l2)) ^ N ≤ ∫ x, lt2fH x ∂rowM N := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  have hPm : Measurable fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) ^ 2 := measurable_rowPw.pow_const 2
  have hP2 : Integrable (fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) ^ 2) (rowM N) :=
    Integrable.of_bound hPm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
        (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _))
  set T1 : (Fin N → ℝ) → ℝ := fun x => if 38 / 100 * (N : ℝ) < lt2L x then (∏ j, clamp01 (x j)) ^ 2 else 0
  set T2 : (Fin N → ℝ) → ℝ := fun x => if lt2L x ≤ lt2x1 * N then (∏ j, clamp01 (x j)) ^ 2 else 0
  have hT1m : Measurable T1 := Measurable.ite (measurableSet_lt measurable_const lt2L_measurable) hPm measurable_const
  have hT2m : Measurable T2 := Measurable.ite (measurableSet_le lt2L_measurable measurable_const) hPm measurable_const
  have hP1 : ∀ x : Fin N → ℝ, |(∏ j, clamp01 (x j)) ^ 2| ≤ 1 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
      (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _)
  have hT1 : Integrable T1 (rowM N) := Integrable.of_bound hT1m.aestronglyMeasurable 1 (ae_of_all _ fun x => by
    simp only [T1, Real.norm_eq_abs]; split_ifs
    · exact hP1 x
    · simp)
  have hT2 : Integrable T2 (rowM N) := Integrable.of_bound hT2m.aestronglyMeasurable 1 (ae_of_all _ fun x => by
    simp only [T2, Real.norm_eq_abs]; split_ifs
    · exact hP1 x
    · simp)
  have heq : (fun x => lt2fH x) = fun x => (∏ j, clamp01 (x j)) ^ 2 - T1 x - T2 x := funext lt2fH_eq
  rw [heq, integral_sub (f := fun x => (∏ j, clamp01 (x j)) ^ 2 - T1 x) (g := T2) (hP2.sub hT1) hT2,
    integral_sub (f := fun x => (∏ j, clamp01 (x j)) ^ 2) (g := T1) hP2 hT1]
  have e0 : ∫ x, (∏ j, clamp01 (x j)) ^ 2 ∂rowM N = (1 / 3 : ℝ) ^ N := by
    rw [integral_rowP_pow' 2]; norm_num
  have i1 : ∫ x, T1 x ∂rowM N ≤ Real.exp (-(l1 * (38 / 100 * N))) * (1 / (3 - l1)) ^ N := by
    calc ∫ x, T1 x ∂rowM N ≤ ∫ x, Real.exp (-(l1 * (38 / 100 * N))) * Real.exp ((l1 - 2) * lt2L x) ∂rowM N :=
          integral_mono hT1 ((lt2_tilt_integrable (by linarith)).const_mul _) fun x => lt2_tail_hi_le hl1 x
      _ = _ := by
          rw [integral_const_mul, lt2_tilt_int (by linarith)]
          congr 2; ring
  have i2 : ∫ x, T2 x ∂rowM N ≤ Real.exp (l2 * (lt2x1 * N)) * (1 / (3 + l2)) ^ N := by
    calc ∫ x, T2 x ∂rowM N ≤ ∫ x, Real.exp (l2 * (lt2x1 * N)) * Real.exp ((-2 - l2) * lt2L x) ∂rowM N :=
          integral_mono hT2 ((lt2_tilt_integrable (by linarith)).const_mul _) fun x => lt2_tail_lo_le hl2 x
      _ = _ := by
          rw [integral_const_mul, lt2_tilt_int (by linarith)]
          congr 2; ring
  rw [e0]; linarith

lemma lt2_exp_neg_le_quarter {c : ℝ} (hc : 4 ≤ c) : Real.exp (-c) ≤ 1 / 4 := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp c])

/-- **`E f ≥ 3^{-N}/2` eventually.** -/
theorem lt2_Ef_half : ∀ᶠ N : ℕ in atTop, (1 / 3 : ℝ) ^ N / 2 ≤ ∫ x, lt2fH x ∂rowM N := by
  filter_upwards [eventually_ge_atTop 450] with N hN
  have hNr : (450 : ℝ) ≤ N := by exact_mod_cast hN
  have h := lt2_Ef_ge (N := N) (l1 := 37 / 100) (l2 := 187 / 100) (by norm_num) (by norm_num) (by norm_num)
  have hx1 := lt2x1_bounds
  have hlog1 : Real.log (300 / 263 : ℝ) ≤ 1317 / 10000 := by
    have hq : Real.log (((300 / 263 : ℚ)) : ℝ) ≤ (((1317 / 10000 : ℚ)) : ℝ) := crLog_le 0 40 (by decide +kernel)
    push_cast at hq; exact hq
  have hlog2 : (4844 / 10000 : ℝ) ≤ Real.log (487 / 300) := by
    have hq : (((4844 / 10000 : ℚ)) : ℝ) ≤ Real.log (((487 / 300 : ℚ)) : ℝ) := crLog_ge 0 40 (by decide +kernel)
    push_cast at hq; exact hq
  have h3 : (0 : ℝ) < (1 / 3 : ℝ) ^ N := by positivity
  have t1 : Real.exp (-(37 / 100 * (38 / 100 * N))) * (1 / (3 - 37 / 100)) ^ N ≤ (1 / 3 : ℝ) ^ N / 4 := by
    have e : (1 / (3 - 37 / 100 : ℝ)) ^ N = (1 / 3 : ℝ) ^ N * Real.exp (N * Real.log (300 / 263)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ← mul_pow]; norm_num
    rw [e, show Real.exp (-(37 / 100 * (38 / 100 * N))) * ((1 / 3 : ℝ) ^ N * Real.exp (N * Real.log (300 / 263))) =
      (1 / 3 : ℝ) ^ N * Real.exp (-(37 / 100 * (38 / 100 * N)) + N * Real.log (300 / 263)) by
        rw [Real.exp_add]; ring]
    have q := lt2_exp_neg_le_quarter (c := 89 / 10000 * N) (by nlinarith)
    have hle : Real.exp (-(37 / 100 * (38 / 100 * N)) + N * Real.log (300 / 263)) ≤ 1 / 4 :=
      (Real.exp_le_exp.2 (by nlinarith)).trans q
    calc (1 / 3 : ℝ) ^ N * Real.exp (-(37 / 100 * (38 / 100 * N)) + N * Real.log (300 / 263))
        ≤ (1 / 3 : ℝ) ^ N * (1 / 4) := mul_le_mul_of_nonneg_left hle h3.le
      _ = (1 / 3 : ℝ) ^ N / 4 := by ring
  have t2 : Real.exp (187 / 100 * (lt2x1 * N)) * (1 / (3 + 187 / 100)) ^ N ≤ (1 / 3 : ℝ) ^ N / 4 := by
    have e : (1 / (3 + 187 / 100 : ℝ)) ^ N = (1 / 3 : ℝ) ^ N * Real.exp (-(N * Real.log (487 / 300))) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), ← inv_pow, ← mul_pow]; norm_num
    rw [e, show Real.exp (187 / 100 * (lt2x1 * N)) * ((1 / 3 : ℝ) ^ N * Real.exp (-(N * Real.log (487 / 300)))) =
      (1 / 3 : ℝ) ^ N * Real.exp (187 / 100 * (lt2x1 * N) + -(N * Real.log (487 / 300))) by
        rw [Real.exp_add]; ring]
    have q := lt2_exp_neg_le_quarter (c := 1 / 10 * N) (by nlinarith)
    have hle : Real.exp (187 / 100 * (lt2x1 * N) + -(N * Real.log (487 / 300))) ≤ 1 / 4 :=
      (Real.exp_le_exp.2 (by nlinarith)).trans q
    calc (1 / 3 : ℝ) ^ N * Real.exp (187 / 100 * (lt2x1 * N) + -(N * Real.log (487 / 300)))
        ≤ (1 / 3 : ℝ) ^ N * (1 / 4) := mul_le_mul_of_nonneg_left hle h3.le
      _ = (1 / 3 : ℝ) ^ N / 4 := by ring
  linarith

end Census
end IIT
