/-
Census, B1 count, WP1 (generic toolkit, no IIT), part 1: the sharp sub-Gaussian bound for centred
uniforms (blueprint `iit-census/lean/B1-W14-count-lean.md` §6; math W13-effect G1).

* `unif_integral_eq`: `∫ f ∂unif = ∫_0^1 f`;
* `sbM_le_sharp`: `E e^{l(U-1/2)} = sinh(l/2)/(l/2) ≤ e^{l²/24}` for every `l` (via `(2k+1)! ≥ 6^k k!`);
* `subGauss_proved : SubGaussStmt`: `P(Σ_{l<n} (U_l - 1/2) ≥ t) ≤ e^{-6t²/n}`;
* `unif_abs_cube`: `E |U - 1/2|³ = 1/32`.
-/
import IIT.Census.B1CntDefs3
import IIT.Census.B1SmallBall

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

/-- Integrals against `unif` are interval integrals over `[0,1]`. -/
lemma unif_integral_eq (f : ℝ → ℝ) : ∫ u, f u ∂unif = ∫ u in (0 : ℝ)..1, f u := by
  unfold unif
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]

/-- Continuous functions are `unif`-integrable. -/
lemma unif_integrable_of_continuous {f : ℝ → ℝ} (hf : Continuous f) : Integrable f unif := by
  unfold unif
  exact hf.integrableOn_Icc

/-- `6^k k! ≤ (2k+1)!`. -/
lemma six_pow_mul_factorial_le (k : ℕ) : 6 ^ k * k.factorial ≤ (2 * k + 1).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (2 * (k + 1) + 1).factorial = (2 * k + 3) * ((2 * k + 2) * (2 * k + 1).factorial) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, Nat.factorial_succ,
        show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ]
    rw [h, pow_succ, Nat.factorial_succ]
    calc 6 ^ k * 6 * ((k + 1) * k.factorial) = (6 * (k + 1)) * (6 ^ k * k.factorial) := by ring
      _ ≤ ((2 * k + 3) * (2 * k + 2)) * (2 * k + 1).factorial :=
          Nat.mul_le_mul (by nlinarith) ih
      _ = _ := by ring

/-- `sinh x ≤ x e^{x²/6}` for `x ≥ 0` (termwise from `(2k+1)! ≥ 6^k k!`). -/
lemma sinh_le_mul_exp_sq {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.exp (x ^ 2 / 6) := by
  have h1 := Real.hasSum_sinh x
  have h2 : HasSum (fun n : ℕ => x * ((x ^ 2 / 6) ^ n / (n.factorial : ℝ)))
      (x * Real.exp (x ^ 2 / 6)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (x ^ 2 / 6)).mul_left x
  refine hasSum_le (fun n => ?_) h1 h2
  have hf : (0 : ℝ) < (6 : ℝ) ^ n * (n.factorial : ℝ) := by positivity
  have hle : (6 : ℝ) ^ n * (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast six_pow_mul_factorial_le n
  have e : x * ((x ^ 2 / 6) ^ n / (n.factorial : ℝ)) = x ^ (2 * n + 1) / ((6 : ℝ) ^ n * n.factorial) := by
    rw [div_pow]; field_simp; ring
  rw [e]
  exact div_le_div_of_nonneg_left (by positivity) hf hle

/-- `sbM l = 2 sinh(l/2)/l` for `l ≠ 0`. -/
lemma sbM_eq_sinh {l : ℝ} (hl : l ≠ 0) : sbM l = 2 * Real.sinh (l / 2) / l := by
  rw [sbM_eq]
  have hd : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun u => Real.exp (l * (u - 1 / 2)) / l) (Real.exp (l * (u - 1 / 2))) u := by
    intro u _
    have := ((((hasDerivAt_id u).sub_const (1 / 2)).const_mul l).exp).div_const l
    exact this.congr_deriv (by simp only [id_eq]; field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _), Real.sinh_eq]
  have e1 : l * (1 - 1 / 2) = l / 2 := by ring
  have e2 : l * (0 - 1 / 2) = -(l / 2) := by ring
  rw [e1, e2]
  ring

/-- **Sharp sub-Gaussian mgf of a centred uniform** (W13-effect G1): `sbM l ≤ e^{l²/24}`. -/
theorem sbM_le_sharp (l : ℝ) : sbM l ≤ Real.exp (l ^ 2 / 24) := by
  rcases eq_or_ne l 0 with rfl | hl
  · rw [sbM_eq]; simp
  wlog hpos : 0 < l generalizing l
  · have hneg : 0 < -l := neg_pos.2 (lt_of_le_of_ne (not_lt.1 hpos) hl)
    have := this (-l) (neg_ne_zero.2 hl) hneg
    rwa [sbM_neg, neg_sq] at this
  rw [sbM_eq_sinh hl, div_le_iff₀ hpos]
  have h := sinh_le_mul_exp_sq (x := l / 2) (by positivity)
  have e : (l / 2) ^ 2 / 6 = l ^ 2 / 24 := by ring
  rw [e] at h
  linarith

lemma unif_mgf (l : ℝ) : ∫ u, Real.exp (l * (u - 1 / 2)) ∂unif = sbM l := by
  rw [unif_integral_eq, sbM_eq]

/-- **WP1a: sharp sub-Gaussian tail of centred uniforms.** -/
theorem subGauss_proved : SubGaussStmt := by
  intro n t ht
  set μ := Measure.pi fun _ : Fin n => unif with hμ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact prob_le_one.trans (by simp)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set lam := 12 * t / n with hlam_def
  have hlam : 0 ≤ lam := by positivity
  set X : (Fin n → ℝ) → ℝ := fun u => ∑ l, (u l - 1 / 2) with hX
  have e : ∀ u : Fin n → ℝ, Real.exp (lam * X u) = ∏ l, Real.exp (lam * (u l - 1 / 2)) := by
    intro u; rw [← Real.exp_sum, hX, Finset.mul_sum]
  have hint : Integrable (fun u => Real.exp (lam * X u)) μ := by
    simp_rw [e]
    exact Integrable.fintype_prod (f := fun _ u => Real.exp (lam * (u - 1 / 2)))
      fun _ => unif_integrable_of_continuous (by fun_prop)
  have hmgf : ProbabilityTheory.mgf X μ lam = sbM lam ^ n := by
    rw [ProbabilityTheory.mgf]
    simp_rw [e]
    rw [integral_fintype_prod_eq_prod (f := fun _ u => Real.exp (lam * (u - 1 / 2)))]
    simp only [unif_mgf, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μ) (X := X) t hlam hint
  rw [hmgf] at hc
  have hs0 : 0 ≤ sbM lam := by have := sbM_ge lam; nlinarith [sq_nonneg lam]
  have hb : Real.exp (-lam * t) * sbM lam ^ n ≤ Real.exp (-(6 * t ^ 2 / n)) := by
    calc Real.exp (-lam * t) * sbM lam ^ n
        ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 / 24) ^ n := by
          gcongr; exact sbM_le_sharp lam
      _ = Real.exp (-lam * t + n * (lam ^ 2 / 24)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ = Real.exp (-(6 * t ^ 2 / n)) := by
          congr 1; rw [hlam_def]; field_simp; ring
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hc.trans hb)

/-- `E |U - 1/2|³ = 1/32`. -/
theorem unif_abs_cube : ∫ u, |u - 1 / 2| ^ 3 ∂unif = 1 / 32 := by
  rw [unif_integral_eq, intervalIntegral.integral_comp_sub_right (fun v => |v| ^ 3)]
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => |v| ^ 3) volume a b :=
    fun a b => (by fun_prop : Continuous fun v : ℝ => |v| ^ 3).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (0 - 1 / 2) 0) (hi 0 (1 - 1 / 2))]
  have h1 : ∫ v in (0 - 1 / 2 : ℝ)..0, |v| ^ 3 = ∫ v in (0 - 1 / 2 : ℝ)..0, -(v ^ 3) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hv
    rw [abs_of_nonpos hv.2]; ring
  have h2 : ∫ v in (0 : ℝ)..(1 - 1 / 2), |v| ^ 3 = ∫ v in (0 : ℝ)..(1 - 1 / 2), v ^ 3 := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hv
    rw [abs_of_nonneg hv.1]
  rw [h1, h2, intervalIntegral.integral_neg, integral_pow, integral_pow]
  norm_num

end

end Census
end IIT
