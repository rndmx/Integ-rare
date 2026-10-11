/-
Census, B1 lemma LT2, module M5: a small-ball lower bound for weighted sums of independent uniforms
(`iit-census/lean/LT2-PLAN.md`; replaces W2 §9.4, no Gaussians).

For `Π(ω) = Σ_β c_β (ω_β - 1/2)` under `Measure.pi unif`, `V = Σ c_β²/12`, `sd = √V`, weights `0 ≤ c_β ≤ sd/(16x)`:

    P(Π ≥ x · sd) ≥ e^{-225 x²} / 4        (x ≥ 1).

Proof: Paley-Zygmund (`θ = 1/2`) for `Z = e^{tΠ}`, `t = 8x/sd`.  By independence `E Z = Π m(t c_β)` and
`E Z² = Π m(2t c_β)` with `m(λ) = E e^{λ(U-1/2)}`; `1 + λ²/48 ≤ m(λ) ≤ e^{λ²/12}` for `|λ| ≤ 1` (reflection gives
`m(λ) = E cosh(λ(U-1/2))`).  Then `log E Z ≥ 16x² - x²/12`, `log E Z² ≤ 256 x²`, and `Z > E Z/2` forces `Π > x sd`.
-/
import IIT.Census.B1RegRSEff

namespace IIT
namespace Census

open MeasureTheory Finset

/-! ### Paley-Zygmund -/

/-- **Paley-Zygmund** for a bounded nonnegative variable, `θ ∈ [0, 1)`. -/
theorem sb_paley_zygmund {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω) {C : ℝ} (hZC : ∀ ω, Z ω ≤ C)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hE : 0 < ∫ ω, Z ω ∂μ) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 / ∫ ω, Z ω ^ 2 ∂μ ≤ μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} := by
  set EZ := ∫ ω, Z ω ∂μ
  set A := {ω | θ * EZ < Z ω}
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hZm
  have hiZ : Integrable Z μ := Integrable.of_bound hZm.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]; exact hZC ω)
  have hiZ2 : Integrable (fun ω => Z ω ^ 2) μ := Integrable.of_bound (hZm.pow_const 2).aestronglyMeasurable
    (C ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hZ0 ω) 2)]
      exact pow_le_pow_left₀ (hZ0 ω) (hZC ω) 2)
  have hiA : Integrable (A.indicator (fun _ => (1 : ℝ))) μ := (integrable_const 1).indicator hAm
  have hu1 : μ.real Set.univ = 1 := by simp [measureReal_def]
  have hE2' : EZ ^ 2 ≤ ∫ ω, Z ω ^ 2 ∂μ := by
    have hpt : ∀ ω, 2 * EZ * Z ω - EZ ^ 2 ≤ Z ω ^ 2 := fun ω => by nlinarith [sq_nonneg (Z ω - EZ)]
    have h := integral_mono ((hiZ.const_mul (2 * EZ)).sub (integrable_const (EZ ^ 2))) hiZ2 hpt
    simp only [Pi.sub_apply] at h
    rw [integral_sub (hiZ.const_mul _) (integrable_const _), integral_const_mul, integral_const, hu1,
      one_smul] at h
    nlinarith
  have hE2 : 0 < ∫ ω, Z ω ^ 2 ∂μ := lt_of_lt_of_le (by positivity) hE2'
  set k := (∫ ω, Z ω ^ 2 ∂μ) / ((1 - θ) * EZ) with hk
  have hk0 : 0 < k := div_pos hE2 (mul_pos (by linarith) hE)
  -- pointwise: Z ≤ θ EZ + Z²/(2k) + (k/2) 1_A
  have hpt : ∀ ω, Z ω ≤ θ * EZ + 1 / (2 * k) * Z ω ^ 2 + k / 2 * A.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hsq : 0 ≤ (Z ω - k) ^ 2 / (2 * k) := by positivity
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have : Z ω ≤ 1 / (2 * k) * Z ω ^ 2 + k / 2 := by
        have e : 1 / (2 * k) * Z ω ^ 2 + k / 2 - Z ω = (Z ω - k) ^ 2 / (2 * k) := by field_simp; ring
        linarith
      have : 0 ≤ θ * EZ := mul_nonneg hθ0 hE.le
      linarith
    · rw [Set.indicator_of_notMem hω]
      have : Z ω ≤ θ * EZ := not_lt.1 hω
      have : 0 ≤ 1 / (2 * k) * Z ω ^ 2 := by positivity
      linarith
  have hint := integral_mono hiZ ((((integrable_const _).add (hiZ2.const_mul _))).add (hiA.const_mul _)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add (f := fun ω => θ * EZ + 1 / (2 * k) * Z ω ^ 2)
      (g := fun ω => k / 2 * A.indicator (fun _ => (1 : ℝ)) ω)
      ((integrable_const _).add (hiZ2.const_mul _)) (hiA.const_mul _),
    integral_add (f := fun _ => θ * EZ) (g := fun ω => 1 / (2 * k) * Z ω ^ 2)
      (integrable_const _) (hiZ2.const_mul _), integral_const, hu1, one_smul,
    integral_const_mul, integral_const_mul, integral_indicator_const (1 : ℝ) hAm, smul_eq_mul, mul_one] at hint
  -- solve for μ(A)
  have hkEZ : 1 / (2 * k) * ∫ ω, Z ω ^ 2 ∂μ = (1 - θ) * EZ / 2 := by
    rw [hk]; field_simp
  rw [hkEZ] at hint
  have hA : (1 - θ) * EZ / k ≤ μ.real A := by
    rw [div_le_iff₀ hk0]; nlinarith
  calc (1 - θ) ^ 2 * EZ ^ 2 / ∫ ω, Z ω ^ 2 ∂μ = (1 - θ) * EZ / k := by
        rw [hk]; field_simp
    _ ≤ _ := hA

/-! ### The one-variable moment generating function -/

/-- `m(λ) = E e^{λ(U - 1/2)}` under `unif`. -/
noncomputable def sbM (l : ℝ) : ℝ := ∫ u, Real.exp (l * (clamp01 u - 1 / 2)) ∂unif

lemma sb_unif_eq_interval (f : ℝ → ℝ) : ∫ u, f (clamp01 u) ∂unif = ∫ u in (0 : ℝ)..1, f u := by
  unfold unif
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  rw [show clamp01 u = u by unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]]

lemma sbM_eq (l : ℝ) : sbM l = ∫ u in (0 : ℝ)..1, Real.exp (l * (u - 1 / 2)) :=
  sb_unif_eq_interval (fun u => Real.exp (l * (u - 1 / 2)))

lemma sb_int_sq : ∫ u in (0 : ℝ)..1, (u - 1 / 2) ^ 2 = 1 / 12 := by
  rw [intervalIntegral.integral_comp_sub_right (fun u => u ^ 2), integral_pow]; norm_num

lemma sb_int_lin : ∫ u in (0 : ℝ)..1, (u - 1 / 2) = 0 := by
  rw [intervalIntegral.integral_comp_sub_right (fun u => u), integral_id]; norm_num

lemma sbM_le {l : ℝ} (hl : |l| ≤ 1) : sbM l ≤ Real.exp (l ^ 2 / 12) := by
  have hpt : ∀ u ∈ Set.uIcc (0 : ℝ) 1, Real.exp (l * (u - 1 / 2)) ≤ 1 + l * (u - 1 / 2) + l ^ 2 * (u - 1 / 2) ^ 2 := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    have hy : |l * (u - 1 / 2)| ≤ 1 := by
      rw [abs_mul]
      have : |u - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
      nlinarith [abs_nonneg l, abs_nonneg (u - 1 / 2)]
    have h := Real.abs_exp_sub_one_sub_id_le hy
    have := (abs_le.1 h).2
    nlinarith
  rw [sbM_eq]
  calc ∫ u in (0 : ℝ)..1, Real.exp (l * (u - 1 / 2))
      ≤ ∫ u in (0 : ℝ)..1, (1 + l * (u - 1 / 2) + l ^ 2 * (u - 1 / 2) ^ 2) :=
        intervalIntegral.integral_mono_on zero_le_one (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun u hu => hpt u (by
            rw [Set.uIcc_of_le zero_le_one]; exact hu)
    _ = 1 + l ^ 2 / 12 := by
        rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_add intervalIntegrable_const (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, sb_int_lin, sb_int_sq]
        simp; ring
    _ ≤ _ := by linarith [Real.add_one_le_exp (l ^ 2 / 12)]

lemma sbM_neg (l : ℝ) : sbM (-l) = sbM l := by
  rw [sbM_eq, sbM_eq]
  have e : (fun u : ℝ => Real.exp (-l * (u - 1 / 2))) = fun u => Real.exp (l * ((1 - u) - 1 / 2)) := by
    funext u; congr 1; ring
  rw [e, intervalIntegral.integral_comp_sub_left (fun v => Real.exp (l * (v - 1 / 2))) (1 : ℝ)]
  norm_num

lemma sbM_ge (l : ℝ) : 1 + l ^ 2 / 48 ≤ sbM l := by
  have hpt : ∀ u ∈ Set.uIcc (0 : ℝ) 1, 2 + l ^ 2 * (u - 1 / 2) ^ 2 / 2 ≤
      Real.exp (l * (u - 1 / 2)) + Real.exp (-l * (u - 1 / 2)) := by
    intro u _
    set x := l * (u - 1 / 2)
    have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
    have h2 := Real.add_one_le_exp (-|x|)
    have hsq : |x| ^ 2 = l ^ 2 * (u - 1 / 2) ^ 2 := by rw [sq_abs]; ring
    have hneg : -l * (u - 1 / 2) = -x := by simp only [x]; ring
    have e : Real.exp |x| + Real.exp (-|x|) = Real.exp x + Real.exp (-l * (u - 1 / 2)) := by
      rw [hneg]
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, neg_neg]; ring
    linarith
  have h2 : 2 * sbM l = sbM l + sbM (-l) := by rw [sbM_neg]; ring
  have hsum : sbM l + sbM (-l) = ∫ u in (0 : ℝ)..1, (Real.exp (l * (u - 1 / 2)) + Real.exp (-l * (u - 1 / 2))) := by
    rw [sbM_eq, sbM_eq, intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hlow : 2 + l ^ 2 / 24 ≤ ∫ u in (0 : ℝ)..1, (Real.exp (l * (u - 1 / 2)) + Real.exp (-l * (u - 1 / 2))) := by
    calc 2 + l ^ 2 / 24 = ∫ u in (0 : ℝ)..1, (2 + l ^ 2 * (u - 1 / 2) ^ 2 / 2) := by
          rw [intervalIntegral.integral_add intervalIntegrable_const (Continuous.intervalIntegrable (by fun_prop) _ _),
            intervalIntegral.integral_div, intervalIntegral.integral_const_mul, sb_int_sq]
          simp; ring
      _ ≤ _ := intervalIntegral.integral_mono_on zero_le_one (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun u hu => hpt u (by
            rw [Set.uIcc_of_le zero_le_one]; exact hu)
  linarith

/-- `1 + a ≥ e^{a - a²}` for `a ≥ 0`. -/
lemma sb_one_add_ge_exp {a : ℝ} (ha : 0 ≤ a) : Real.exp (a - a ^ 2) ≤ 1 + a := by
  have h1 : 0 < 1 + a := by linarith
  rw [← Real.exp_log h1]
  apply Real.exp_le_exp.2
  have := Real.one_sub_inv_le_log_of_pos h1
  have h2 : a - a ^ 2 ≤ 1 - (1 + a)⁻¹ := by
    rw [show 1 - (1 + a)⁻¹ = a / (1 + a) by field_simp; ring, le_div_iff₀ h1]
    nlinarith [sq_nonneg a, pow_nonneg ha 3]
  linarith

/-! ### The small ball -/

variable {B : Type*} [Fintype B]

/-- The weighted sum `Σ_β c_β (ω_β - 1/2)`. -/
noncomputable def sbPi (c : B → ℝ) (ω : B → ℝ) : ℝ := ∑ β, c β * (clamp01 (ω β) - 1 / 2)

lemma sb_unif_prob : IsProbabilityMeasure unif := ⟨by unfold unif; simp⟩

lemma sb_mgf (c : B → ℝ) (t : ℝ) :
    ∫ ω, Real.exp (t * sbPi c ω) ∂(Measure.pi fun _ : B => unif) = ∏ β, sbM (t * c β) := by
  have e : ∀ ω : B → ℝ, Real.exp (t * sbPi c ω) = ∏ β, Real.exp (t * c β * (clamp01 (ω β) - 1 / 2)) := by
    intro ω
    rw [← Real.exp_sum]; unfold sbPi; congr 1; rw [Finset.mul_sum]; congr 1; funext β; ring
  simp_rw [e]
  rw [integral_fintype_prod_eq_prod (f := fun β u => Real.exp (t * c β * (clamp01 u - 1 / 2)))]
  rfl

/-- **Small ball.** -/
theorem small_ball (c : B → ℝ) (hc0 : ∀ β, 0 ≤ c β) {x V : ℝ} (hx : 1 ≤ x) (hV : V = ∑ β, c β ^ 2 / 12)
    (hV0 : 0 < V) (hb : ∀ β, c β ≤ Real.sqrt V / (16 * x)) :
    ENNReal.ofReal (Real.exp (-(225 * x ^ 2)) / 4) ≤
      (Measure.pi fun _ : B => unif) {ω | x * Real.sqrt V ≤ sbPi c ω} := by
  haveI := sb_unif_prob
  set μ := Measure.pi fun _ : B => unif
  set sd := Real.sqrt V with hsd
  have hsd0 : 0 < sd := Real.sqrt_pos.2 hV0
  set t := 8 * x / sd with ht
  have ht0 : 0 < t := by positivity
  set lam : B → ℝ := fun β => t * c β
  have hlam0 : ∀ β, 0 ≤ lam β := fun β => mul_nonneg ht0.le (hc0 β)
  have hlam : ∀ β, lam β ≤ 1 / 2 := by
    intro β
    have := hb β
    calc lam β = 8 * x / sd * c β := rfl
      _ ≤ 8 * x / sd * (sd / (16 * x)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / 2 := by field_simp; ring
  -- `Σ λ² = 768 x²`
  have hsum2 : ∑ β, lam β ^ 2 = 768 * x ^ 2 := by
    have : ∑ β, lam β ^ 2 = t ^ 2 * (12 * V) := by
      rw [hV, Finset.mul_sum, Finset.mul_sum]; congr 1; funext β; simp only [lam]; ring
    rw [this, ht, div_pow, Real.sq_sqrt hV0.le]; field_simp; ring
  have hsum4 : ∑ β, lam β ^ 4 ≤ 192 * x ^ 2 := by
    calc ∑ β, lam β ^ 4 ≤ ∑ β, (1 / 4) * lam β ^ 2 := Finset.sum_le_sum fun β _ => by
          have h1 := hlam β; have h0 := hlam0 β
          have : lam β ^ 2 ≤ 1 / 4 := by nlinarith
          nlinarith [pow_nonneg h0 2]
      _ = 192 * x ^ 2 := by rw [← Finset.mul_sum, hsum2]; ring
  -- bounds on `E Z` and `E Z²`
  set Z : (B → ℝ) → ℝ := fun ω => Real.exp (t * sbPi c ω) with hZ
  have hEZ : ∫ ω, Z ω ∂μ = ∏ β, sbM (lam β) := sb_mgf c t
  have hEZ2 : ∫ ω, Z ω ^ 2 ∂μ = ∏ β, sbM ((2 * t) * c β) := by
    rw [← sb_mgf c (2 * t)]; congr 1; funext ω; simp only [hZ]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hlow : Real.exp (16 * x ^ 2 - x ^ 2 / 12) ≤ ∫ ω, Z ω ∂μ := by
    rw [hEZ]
    calc Real.exp (16 * x ^ 2 - x ^ 2 / 12) ≤ Real.exp (∑ β, (lam β ^ 2 / 48 - (lam β ^ 2 / 48) ^ 2)) := by
          apply Real.exp_le_exp.2
          rw [Finset.sum_sub_distrib, ← Finset.sum_div]
          have : ∑ β, (lam β ^ 2 / 48) ^ 2 = (∑ β, lam β ^ 4) / 2304 := by
            rw [Finset.sum_div]; congr 1; funext β; ring
          rw [this, hsum2]; linarith
      _ = ∏ β, Real.exp (lam β ^ 2 / 48 - (lam β ^ 2 / 48) ^ 2) := Real.exp_sum _ _
      _ ≤ ∏ β, sbM (lam β) := Finset.prod_le_prod (fun β _ => (Real.exp_pos _).le) fun β _ =>
          (sb_one_add_ge_exp (by positivity)).trans (by have := sbM_ge (lam β); linarith)
  have hup : ∫ ω, Z ω ^ 2 ∂μ ≤ Real.exp (256 * x ^ 2) := by
    rw [hEZ2]
    calc ∏ β, sbM ((2 * t) * c β) ≤ ∏ β, Real.exp ((2 * lam β) ^ 2 / 12) :=
          Finset.prod_le_prod (fun β _ => by
            have := sbM_ge ((2 * t) * c β); nlinarith [sq_nonneg ((2 * t) * c β)]) fun β _ => by
            have h := sbM_le (l := (2 * t) * c β) (by
              rw [abs_of_nonneg (by have := hlam0 β; simp only [lam] at this; nlinarith)]
              have := hlam β; simp only [lam] at this; linarith)
            simpa [lam, mul_assoc] using h
      _ = Real.exp (∑ β, (2 * lam β) ^ 2 / 12) := (Real.exp_sum _ _).symm
      _ = Real.exp (256 * x ^ 2) := by
          congr 1
          have : ∑ β, (2 * lam β) ^ 2 / 12 = (∑ β, lam β ^ 2) / 3 := by
            rw [Finset.sum_div]; congr 1; funext β; ring
          rw [this, hsum2]; ring
  -- Paley-Zygmund
  have hZm : Measurable Z := by
    simp only [hZ, sbPi]
    exact Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun β _ =>
      measurable_const.mul ((clamp01_measurable.comp (measurable_pi_apply β)).sub measurable_const)))
  have hZC : ∀ ω, Z ω ≤ Real.exp (t * ∑ β, c β) := by
    intro ω
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ ht0.le
    unfold sbPi
    refine Finset.sum_le_sum fun β _ => ?_
    have := clamp01_le_one (ω β); have := clamp01_nonneg (ω β); have := hc0 β
    nlinarith
  have hE0 : 0 < ∫ ω, Z ω ∂μ := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hpz := sb_paley_zygmund μ hZm (fun ω => (Real.exp_pos _).le) hZC (θ := 1 / 2) (by norm_num)
    (by norm_num) hE0
  have hiZ : Integrable Z μ := Integrable.of_bound hZm.aestronglyMeasurable _
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hZC ω)
  have hiZ2 : Integrable (fun ω => Z ω ^ 2) μ :=
    Integrable.of_bound (hZm.pow_const 2).aestronglyMeasurable (Real.exp (t * ∑ β, c β) ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.exp_pos _).le 2)]
        exact pow_le_pow_left₀ (Real.exp_pos _).le (hZC ω) 2)
  have hE2pos : 0 < ∫ ω, Z ω ^ 2 ∂μ := by
    have hpos : ∀ ω, 0 < Z ω ^ 2 := fun ω => pow_pos (Real.exp_pos _) 2
    exact integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hiZ2 |>.2 (by
      rw [Function.support_eq_univ (fun ω => (hpos ω).ne')]; simp)
  have hratio : Real.exp (-(225 * x ^ 2)) / 4 ≤ (1 - 1 / 2) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 / ∫ ω, Z ω ^ 2 ∂μ := by
    rw [le_div_iff₀ hE2pos]
    have h1 : Real.exp (16 * x ^ 2 - x ^ 2 / 12) ^ 2 ≤ (∫ ω, Z ω ∂μ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hlow 2
    have h2 : Real.exp (-(225 * x ^ 2)) * Real.exp (256 * x ^ 2) ≤ Real.exp (16 * x ^ 2 - x ^ 2 / 12) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]; apply Real.exp_le_exp.2; push_cast; nlinarith
    have h3 : Real.exp (-(225 * x ^ 2)) / 4 * ∫ ω, Z ω ^ 2 ∂μ ≤
        Real.exp (-(225 * x ^ 2)) / 4 * Real.exp (256 * x ^ 2) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    nlinarith
  -- the event
  have hsub : {ω | 1 / 2 * ∫ ω, Z ω ∂μ < Z ω} ⊆ {ω | x * sd ≤ sbPi c ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h1 : Real.exp (8 * x ^ 2) < Z ω := by
      refine lt_of_le_of_lt ?_ hω
      have : Real.exp (8 * x ^ 2) * 2 ≤ Real.exp (16 * x ^ 2 - x ^ 2 / 12) := by
        rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have := Real.log_two_lt_d9; nlinarith
      linarith
    have h2 : 8 * x ^ 2 < t * sbPi c ω := by
      simp only [hZ] at h1; exact Real.exp_lt_exp.1 h1
    have h3 : x * sd = 8 * x ^ 2 / t := by rw [ht]; field_simp
    rw [h3, div_le_iff₀ ht0]; linarith
  calc ENNReal.ofReal (Real.exp (-(225 * x ^ 2)) / 4)
      ≤ ENNReal.ofReal (μ.real {ω | 1 / 2 * ∫ ω, Z ω ∂μ < Z ω}) := ENNReal.ofReal_le_ofReal (hratio.trans hpz)
    _ = μ {ω | 1 / 2 * ∫ ω, Z ω ∂μ < Z ω} := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := measure_mono hsub

end Census
end IIT

#print axioms IIT.Census.small_ball
