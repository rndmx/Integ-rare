/-
Census: smooth test functions for sup-norm boxes and their Lindeberg bounds.

For a centre `c : Fin d → ℝ`, a radius `r` and a width `ε > 0`, the factor
`t ↦ ψ((t - c - r)/ε + b) ψ((c - r - t)/ε + b)` is `C³` with `|φ^(n)| ≤ (2 Kψ/ε)^n` (Leibniz), so
the product `tp_boxF c r ε b` is an admissible Lindeberg test function (`tp_factors_box`).  With
`b = 0` it sandwiches the box of radius `r` between itself and the box of radius `r + ε`; with
`b = 1` it lies between the boxes of radii `r - ε` and `r` (`tp_box_*`).
-/
import IIT.Census.Lindeberg
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

variable {d : ℕ}

/-- The sup-norm box of centre `c` and radius `r`. -/
def tp_ball (c : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) := {x | ∀ j, |x j - c j| ≤ r}

/-- One factor of the smooth box function. -/
def tp_bfac (c r ε b t : ℝ) : ℝ :=
  lind_psi ((t - (c + r)) / ε + b) * lind_psi (((c - r) - t) / ε + b)

/-- The smooth box function. -/
def tp_boxF (c : Fin d → ℝ) (r ε b : ℝ) (x : Fin d → ℝ) : ℝ := ∏ j, tp_bfac (c j) r ε b (x j)

lemma tp_boxF_eq (c : Fin d → ℝ) (r ε b : ℝ) :
    tp_boxF c r ε b = lind_F (fun j t => tp_bfac (c j) r ε b t) := rfl

lemma tp_bfac_nonneg (c r ε b t : ℝ) : 0 ≤ tp_bfac c r ε b t :=
  mul_nonneg (lind_psi_nonneg _) (lind_psi_nonneg _)

lemma tp_bfac_le_one (c r ε b t : ℝ) : tp_bfac c r ε b t ≤ 1 := by
  unfold tp_bfac
  have h1 := lind_psi_le_one ((t - (c + r)) / ε + b)
  have h2 := lind_psi_nonneg ((t - (c + r)) / ε + b)
  have h3 := lind_psi_le_one (((c - r) - t) / ε + b)
  have h4 := lind_psi_nonneg (((c - r) - t) / ε + b)
  nlinarith

lemma tp_boxF_nonneg (c : Fin d → ℝ) (r ε b : ℝ) (x : Fin d → ℝ) : 0 ≤ tp_boxF c r ε b x :=
  prod_nonneg fun _ _ => tp_bfac_nonneg _ _ _ _ _

lemma tp_boxF_le_one (c : Fin d → ℝ) (r ε b : ℝ) (x : Fin d → ℝ) : tp_boxF c r ε b x ≤ 1 :=
  prod_le_one (fun _ _ => tp_bfac_nonneg _ _ _ _ _) fun _ _ => tp_bfac_le_one _ _ _ _ _

/-- The reflected cut-off `t ↦ ψ((a - t)/ε + b)` has `|g^(n)| ≤ (Kψ/ε)^n`. -/
lemma tp_psi_refl_bound (a b : ℝ) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≤ 3) (t : ℝ) :
    |iteratedDeriv n (fun t => lind_psi ((a - t) / ε + b)) t| ≤ (lind_Kpsi / ε) ^ n := by
  have hfun : (fun t => lind_psi ((a - t) / ε + b))
      = fun t => (fun s => lind_psi (s + (a / ε + b))) ((-ε⁻¹) * t) := by
    funext t; beta_reduce; congr 1; field_simp; ring
  have hcd : ContDiff ℝ n (fun s => lind_psi (s + (a / ε + b))) :=
    (lind_psi_contDiff_nat n).comp (contDiff_id.add contDiff_const)
  rw [hfun, iteratedDeriv_comp_const_mul hcd, iteratedDeriv_comp_add_const]
  calc |(-ε⁻¹) ^ n * iteratedDeriv n lind_psi ((-ε⁻¹) * t + (a / ε + b))|
      = ε⁻¹ ^ n * |iteratedDeriv n lind_psi ((-ε⁻¹) * t + (a / ε + b))| := by
        rw [abs_mul, abs_pow, abs_neg, abs_inv, abs_of_pos hε]
    _ ≤ ε⁻¹ ^ n * lind_Kpsi ^ n :=
        mul_le_mul_of_nonneg_left (lind_abs_iteratedDeriv_psi_le hn _) (by positivity)
    _ = (lind_Kpsi / ε) ^ n := by rw [div_eq_mul_inv, mul_pow, mul_comm]

lemma tp_psi_shift_bound (a b : ℝ) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≤ 3) (t : ℝ) :
    |iteratedDeriv n (fun t => lind_psi ((t - a) / ε + b)) t| ≤ (lind_Kpsi / ε) ^ n :=
  (lind_factors_psi (d := 1) (fun _ => a) hε b).bound 0 n t hn

lemma tp_psi_shift_contDiff (a b ε : ℝ) : ContDiff ℝ 3 (fun t => lind_psi ((t - a) / ε + b)) :=
  (lind_psi_contDiff_nat 3).comp (((contDiff_id.sub contDiff_const).div_const _).add contDiff_const)

lemma tp_psi_refl_contDiff (a b ε : ℝ) : ContDiff ℝ 3 (fun t => lind_psi ((a - t) / ε + b)) :=
  (lind_psi_contDiff_nat 3).comp (((contDiff_const.sub contDiff_id).div_const _).add contDiff_const)

/-- Leibniz bound for a product of two functions with geometric derivative bounds. -/
lemma tp_leibniz {f g : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) {K : ℝ} (hK : 0 ≤ K)
    (hfb : ∀ n ≤ 3, ∀ t, |iteratedDeriv n f t| ≤ K ^ n)
    (hgb : ∀ n ≤ 3, ∀ t, |iteratedDeriv n g t| ≤ K ^ n) {n : ℕ} (hn : n ≤ 3) (t : ℝ) :
    |iteratedDeriv n (fun y => f y * g y) t| ≤ (2 * K) ^ n := by
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_mul_le hf hg t (by exact_mod_cast hn)).trans ?_
  rw [two_mul, add_pow]
  refine sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := hfb i (hi'.trans hn) t
  have h2 := hgb (n - i) ((Nat.sub_le n i).trans hn) t
  have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  calc (n.choose i : ℝ) * |iteratedDeriv i f t| * |iteratedDeriv (n - i) g t|
      ≤ (n.choose i : ℝ) * K ^ i * K ^ (n - i) := by
        gcongr
    _ = K ^ i * K ^ (n - i) * (n.choose i : ℝ) := by ring

/-- **The box factors are admissible** with `K = 2 Kψ / ε`. -/
lemma tp_factors_box (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ℝ) :
    LindFactors (fun j t => tp_bfac (c j) r ε b t) (2 * (lind_Kpsi / ε)) where
  nonneg := by have := lind_Kpsi_pos; positivity
  contDiff j := by
    have h1 := tp_psi_shift_contDiff (c j + r) b ε
    have h2 := tp_psi_refl_contDiff (c j - r) b ε
    exact h1.mul h2
  bound j n t hn := by
    have h1 := tp_psi_shift_contDiff (c j + r) b ε
    have h2 := tp_psi_refl_contDiff (c j - r) b ε
    exact tp_leibniz h1 h2 (by have := lind_Kpsi_pos; positivity)
      (fun n hn t => tp_psi_shift_bound _ b hε hn t) (fun n hn t => tp_psi_refl_bound _ b hε hn t)
      hn t

lemma continuous_tp_boxF (c : Fin d → ℝ) (r ε b : ℝ) : Continuous (tp_boxF c r ε b) := by
  unfold tp_boxF tp_bfac
  exact continuous_finsetProd _ fun j _ =>
    (lind_psi_continuous.comp ((((continuous_apply j).sub continuous_const).div_const _).add
      continuous_const)).mul
    (lind_psi_continuous.comp (((continuous_const.sub (continuous_apply j)).div_const _).add
      continuous_const))

lemma measurable_tp_boxF (c : Fin d → ℝ) (r ε b : ℝ) : Measurable (tp_boxF c r ε b) :=
  (continuous_tp_boxF c r ε b).measurable

/-! ### Values of the factors -/

lemma tp_bfac0_one {c r ε t : ℝ} (hε : 0 < ε) (h : |t - c| ≤ r) : tp_bfac c r ε 0 t = 1 := by
  rw [abs_le] at h
  unfold tp_bfac
  rw [lind_psi_of_nonpos, lind_psi_of_nonpos, mul_one]
  · rw [add_zero]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  · rw [add_zero]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le

lemma tp_bfac0_zero {c r ε t : ℝ} (hε : 0 < ε) (h : r + ε < |t - c|) : tp_bfac c r ε 0 t = 0 := by
  unfold tp_bfac
  rcases le_or_gt 0 (t - c) with h0 | h0
  · rw [abs_of_nonneg h0] at h
    rw [lind_psi_of_one_le, zero_mul]
    rw [add_zero, le_div_iff₀ hε]; linarith
  · rw [abs_of_neg h0] at h
    rw [lind_psi_of_one_le (t := ((c - r) - t) / ε + 0), mul_zero]
    rw [add_zero, le_div_iff₀ hε]; linarith

lemma tp_bfac1_one {c r ε t : ℝ} (hε : 0 < ε) (h : |t - c| ≤ r - ε) : tp_bfac c r ε 1 t = 1 := by
  rw [abs_le] at h
  unfold tp_bfac
  have e1 : (t - (c + r)) / ε + 1 ≤ 0 := by
    have : (t - (c + r)) / ε ≤ -1 := by rw [div_le_iff₀ hε]; linarith
    linarith
  have e2 : ((c - r) - t) / ε + 1 ≤ 0 := by
    have : ((c - r) - t) / ε ≤ -1 := by rw [div_le_iff₀ hε]; linarith
    linarith
  rw [lind_psi_of_nonpos e1, lind_psi_of_nonpos e2, mul_one]

lemma tp_bfac1_zero {c r ε t : ℝ} (hε : 0 < ε) (h : r < |t - c|) : tp_bfac c r ε 1 t = 0 := by
  unfold tp_bfac
  rcases le_or_gt 0 (t - c) with h0 | h0
  · rw [abs_of_nonneg h0] at h
    rw [lind_psi_of_one_le, zero_mul]
    have : 0 < (t - (c + r)) / ε := div_pos (by linarith) hε
    linarith
  · rw [abs_of_neg h0] at h
    rw [lind_psi_of_one_le (t := ((c - r) - t) / ε + 1), mul_zero]
    have : 0 < ((c - r) - t) / ε := div_pos (by linarith) hε
    linarith

/-! ### The sandwich -/

lemma tp_ind_le_boxF0 (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    (tp_ball c r).indicator 1 x ≤ tp_boxF c r ε 0 x := by
  by_cases h : x ∈ tp_ball c r
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    exact le_of_eq (prod_eq_one fun j _ => tp_bfac0_one hε (h j)).symm
  · rw [Set.indicator_of_notMem h]; exact tp_boxF_nonneg _ _ _ _ _

lemma tp_boxF0_le_ind (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    tp_boxF c r ε 0 x ≤ (tp_ball c (r + ε)).indicator 1 x := by
  by_cases h : x ∈ tp_ball c (r + ε)
  · rw [Set.indicator_of_mem h, Pi.one_apply]; exact tp_boxF_le_one _ _ _ _ _
  · rw [Set.indicator_of_notMem h]
    obtain ⟨j, hj⟩ := not_forall.1 h
    exact le_of_eq (prod_eq_zero (mem_univ j) (tp_bfac0_zero hε (not_le.1 hj)))

lemma tp_ind_le_boxF1 (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    (tp_ball c (r - ε)).indicator 1 x ≤ tp_boxF c r ε 1 x := by
  by_cases h : x ∈ tp_ball c (r - ε)
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    exact le_of_eq (prod_eq_one fun j _ => tp_bfac1_one hε (h j)).symm
  · rw [Set.indicator_of_notMem h]; exact tp_boxF_nonneg _ _ _ _ _

lemma tp_boxF1_le_ind (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    tp_boxF c r ε 1 x ≤ (tp_ball c r).indicator 1 x := by
  by_cases h : x ∈ tp_ball c r
  · rw [Set.indicator_of_mem h, Pi.one_apply]; exact tp_boxF_le_one _ _ _ _ _
  · rw [Set.indicator_of_notMem h]
    obtain ⟨j, hj⟩ := not_forall.1 h
    exact le_of_eq (prod_eq_zero (mem_univ j) (tp_bfac1_zero hε (not_le.1 hj)))

lemma tp_measurableSet_ball (c : Fin d → ℝ) (r : ℝ) : MeasurableSet (tp_ball c r) := by
  have : tp_ball c r = ⋂ j, (fun x : Fin d → ℝ => |x j - c j|) ⁻¹' Set.Iic r := by
    ext x; simp [tp_ball]
  rw [this]
  exact MeasurableSet.iInter fun j => (by fun_prop : Measurable _) measurableSet_Iic

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {g : Ω → Fin d → ℝ}

lemma tp_integrable_boxF (hg : Measurable g) (c : Fin d → ℝ) (r ε b : ℝ) :
    Integrable (fun ω => tp_boxF c r ε b (g ω)) μ :=
  lind_integrable_of_abs_le_one ((measurable_tp_boxF c r ε b).comp hg) fun ω =>
    abs_le.2 ⟨by linarith [tp_boxF_nonneg c r ε b (g ω)], tp_boxF_le_one c r ε b (g ω)⟩

omit [IsFiniteMeasure μ] in
lemma tp_integral_ind_ball (hg : Measurable g) (c : Fin d → ℝ) (r : ℝ) :
    ∫ ω, (tp_ball c r).indicator (1 : (Fin d → ℝ) → ℝ) (g ω) ∂μ = μ.real (g ⁻¹' tp_ball c r) := by
  rw [← integral_indicator_one (hg (tp_measurableSet_ball c r))]
  rfl

lemma tp_integrable_ind_ball (hg : Measurable g) (c : Fin d → ℝ) (r : ℝ) :
    Integrable (fun ω => (tp_ball c r).indicator (1 : (Fin d → ℝ) → ℝ) (g ω)) μ :=
  (integrable_const (1 : ℝ)).indicator (hg (tp_measurableSet_ball c r))

/-- `P(g ∈ B(c, r)) ≤ E boxF₀(g)`. -/
lemma tp_real_le_boxF0 (hg : Measurable g) (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ.real (g ⁻¹' tp_ball c r) ≤ ∫ ω, tp_boxF c r ε 0 (g ω) ∂μ := by
  rw [← tp_integral_ind_ball hg]
  exact integral_mono (tp_integrable_ind_ball hg c r) (tp_integrable_boxF hg c r ε 0)
    fun ω => tp_ind_le_boxF0 c r hε (g ω)

/-- `E boxF₀(g) ≤ P(g ∈ B(c, r + ε))`. -/
lemma tp_boxF0_le_real (hg : Measurable g) (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, tp_boxF c r ε 0 (g ω) ∂μ ≤ μ.real (g ⁻¹' tp_ball c (r + ε)) := by
  rw [← tp_integral_ind_ball hg]
  exact integral_mono (tp_integrable_boxF hg c r ε 0) (tp_integrable_ind_ball hg c _)
    fun ω => tp_boxF0_le_ind c r hε (g ω)

/-- `P(g ∈ B(c, r - ε)) ≤ E boxF₁(g)`. -/
lemma tp_real_le_boxF1 (hg : Measurable g) (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ.real (g ⁻¹' tp_ball c (r - ε)) ≤ ∫ ω, tp_boxF c r ε 1 (g ω) ∂μ := by
  rw [← tp_integral_ind_ball hg]
  exact integral_mono (tp_integrable_ind_ball hg c _) (tp_integrable_boxF hg c r ε 1)
    fun ω => tp_ind_le_boxF1 c r hε (g ω)

/-- `E boxF₁(g) ≤ P(g ∈ B(c, r))`. -/
lemma tp_boxF1_le_real (hg : Measurable g) (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, tp_boxF c r ε 1 (g ω) ∂μ ≤ μ.real (g ⁻¹' tp_ball c r) := by
  rw [← tp_integral_ind_ball hg]
  exact integral_mono (tp_integrable_boxF hg c r ε 1) (tp_integrable_ind_ball hg c r)
    fun ω => tp_boxF1_le_ind c r hε (g ω)

end Expect

/-- **Lindeberg bound for the smooth box functions** (`K = 2 Kψ / ε`). -/
theorem tp_box_pi {ν γ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hν0 : ∀ j, ∫ x, x j ∂ν = 0) (hγ0 : ∀ j, ∫ x, x j ∂γ = 0)
    (hν3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν)
    (hγ3 : Integrable (fun x => (∑ j, |x j|) ^ 3) γ)
    (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ℝ) (B : ℕ) :
    |∫ x, tp_boxF c r ε b (∑ β, x β) ∂(Measure.pi fun _ : Fin B => ν)
      - ∫ x, tp_boxF c r ε b (∑ β, x β) ∂(Measure.pi fun _ : Fin B => γ)| ≤
      B * ((2 * (lind_Kpsi / ε)) ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂ν - ∫ x, x j * x k ∂γ| +
        (2 * (lind_Kpsi / ε)) ^ 3 / 6 *
          (∫ x, (∑ j, |x j|) ^ 3 ∂ν + ∫ x, (∑ j, |x j|) ^ 3 ∂γ)) := by
  rw [tp_boxF_eq]
  exact lind_pi (tp_factors_box c r hε b) hν0 hγ0 hν3 hγ3 B

end

end Census
end IIT
