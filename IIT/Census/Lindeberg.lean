/-
Lindeberg's replacement method with smooth test functions of product form.

* A third-order Taylor formula for products `x ↦ ∏ j, φ j (x j)` of one-variable `C³` functions
  with `|φ j| ≤ 1` and `|φ j ^ (m)| ≤ K ^ m`: the remainder is at most `(K ‖h‖₁)³ / 6`.
* The Lindeberg comparison: for two centred laws `ν, γ` on `ℝ^d` with finite third absolute
  moments, the expectations of such a test function at the sum of `B` iid vectors under `ν` and
  under `γ` differ by at most `B` times a covariance-mismatch term plus a third-moment term.
* Smooth orthant functions `orthUp`, `orthLow` built from `ψ = 1 - smoothTransition`, which
  sandwich the indicator of a coordinate orthant, and the corresponding Lindeberg bounds.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

namespace IIT
namespace Census

open MeasureTheory Finset Set Topology

noncomputable section

/-! ### One-variable Taylor bound with explicit derivatives -/

/-- Third-order Taylor bound on `[0,1]` for a function with explicit successive derivatives. -/
lemma lind_taylor3 {g g1 g2 g3 : ℝ → ℝ} {M : ℝ}
    (h0 : ∀ t, HasDerivAt g (g1 t) t) (h1 : ∀ t, HasDerivAt g1 (g2 t) t)
    (h2 : ∀ t, HasDerivAt g2 (g3 t) t) (hM : ∀ t ∈ Icc (0 : ℝ) 1, |g3 t| ≤ M) :
    |g 1 - g 0 - g1 0 - g2 0 / 2| ≤ M / 6 := by
  have hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖g2 t - g2 0‖ ≤ M * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment (f := g2) (f' := g3)
      (fun t _ => (h2 t).continuousAt.continuousWithinAt)
      (fun t _ => (h2 t).hasDerivWithinAt) (fun t ht => hM t (Ico_subset_Icc_self ht))
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖g1 t - g1 0 - g2 0 * t‖ ≤ M * t ^ 2 / 2 := by
    have hd : ∀ t, HasDerivAt (fun t => g1 t - g1 0 - g2 0 * t) (g2 t - g2 0) t := by
      intro t
      have := ((h1 t).sub_const (g1 0)).fun_sub ((hasDerivAt_id t).const_mul (g2 0))
      simpa using this
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1)
      (f := fun t => g1 t - g1 0 - g2 0 * t) (f' := fun t => g2 t - g2 0)
      (B := fun t => M * t ^ 2 / 2) (B' := fun t => M * t)
      (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt)
      (by simp) ?_ ?_
    · intro t
      exact (((hasDerivAt_pow 2 t).const_mul M).div_const 2).congr_deriv (by push_cast; ring)
    · intro t ht
      have := hA t (Ico_subset_Icc_self ht)
      simpa using this
  have hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g t - g 0 - g1 0 * t - g2 0 * t ^ 2 / 2‖ ≤ M * t ^ 3 / 6 := by
    have hd : ∀ t, HasDerivAt (fun t => g t - g 0 - g1 0 * t - g2 0 * t ^ 2 / 2)
        (g1 t - g1 0 - g2 0 * t) t := by
      intro t
      have := (((h0 t).sub_const (g 0)).fun_sub ((hasDerivAt_id t).const_mul (g1 0))).fun_sub
        (((hasDerivAt_pow 2 t).const_mul (g2 0)).div_const 2)
      exact this.congr_deriv (by simp; ring)
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1)
      (f := fun t => g t - g 0 - g1 0 * t - g2 0 * t ^ 2 / 2)
      (f' := fun t => g1 t - g1 0 - g2 0 * t)
      (B := fun t => M * t ^ 3 / 6) (B' := fun t => M * t ^ 2 / 2)
      (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt)
      (by simp) ?_ ?_
    · intro t
      exact (((hasDerivAt_pow 3 t).const_mul M).div_const 6).congr_deriv (by push_cast; ring)
    · intro t ht
      exact hB t (Ico_subset_Icc_self ht)
  have := hC 1 ⟨zero_le_one, le_rfl⟩
  simpa using this

/-! ### Taylor formula for products -/

variable {d : ℕ}

/-- The product test function `x ↦ ∏ j, φ j (x j)`. -/
def lind_F (φ : Fin d → ℝ → ℝ) (x : Fin d → ℝ) : ℝ := ∏ j, φ j (x j)

/-- The mixed partial derivative of multi-order `o` of `lind_F φ`. -/
def lind_D (φ : Fin d → ℝ → ℝ) (o : Fin d → ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ j, iteratedDeriv (o j) (φ j) (x j)

/-- The linear Taylor term of `lind_F φ` at `u`, applied to `h`. -/
def lind_lin (φ : Fin d → ℝ → ℝ) (u h : Fin d → ℝ) : ℝ :=
  ∑ j, lind_D φ (Pi.single j 1) u * h j

/-- The Hessian entries of `lind_F φ` at `u`. -/
def lind_q (φ : Fin d → ℝ → ℝ) (u : Fin d → ℝ) (j k : Fin d) : ℝ :=
  lind_D φ (Pi.single j 1 + Pi.single k 1) u

/-- The quadratic Taylor term `Σ_{j,k} q_{jk}(u) h_j h_k`. -/
def lind_quad (φ : Fin d → ℝ → ℝ) (u h : Fin d → ℝ) : ℝ :=
  ∑ j, ∑ k, lind_q φ u j k * (h j * h k)

/-- Admissible factors: each `φ j` is `C³`, and `|φ j ^ (n)| ≤ K ^ n` for `n ≤ 3`
(in particular `|φ j| ≤ 1`). -/
structure LindFactors (φ : Fin d → ℝ → ℝ) (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  contDiff : ∀ j, ContDiff ℝ 3 (φ j)
  bound : ∀ j (n : ℕ) (t : ℝ), n ≤ 3 → |iteratedDeriv n (φ j) t| ≤ K ^ n

lemma lind_single_le (l j : Fin d) : (Pi.single l 1 : Fin d → ℕ) j ≤ 1 := by
  rw [Pi.single_apply]; split_ifs <;> simp

lemma lind_hasDerivAt_D {φ : Fin d → ℝ → ℝ} (hφ : ∀ j, ContDiff ℝ 3 (φ j)) (o : Fin d → ℕ)
    (ho : ∀ j, o j ≤ 2) (u h : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun s => lind_D φ o (fun j => u j + s * h j))
      (∑ l, h l * lind_D φ (o + Pi.single l 1) (fun j => u j + t * h j)) t := by
  classical
  have hj : ∀ j ∈ (univ : Finset (Fin d)),
      HasDerivAt (fun s => iteratedDeriv (o j) (φ j) (u j + s * h j))
        (iteratedDeriv (o j + 1) (φ j) (u j + t * h j) * h j) t := by
    intro j _
    have hd : Differentiable ℝ (iteratedDeriv (o j) (φ j)) :=
      (hφ j).differentiable_iteratedDeriv (o j)
        (by have := ho j; exact_mod_cast (show o j < 3 by omega))
    have h1 : HasDerivAt (iteratedDeriv (o j) (φ j))
        (iteratedDeriv (o j + 1) (φ j) (u j + t * h j)) (u j + t * h j) := by
      rw [iteratedDeriv_succ]; exact (hd _).hasDerivAt
    have h2 : HasDerivAt (fun s => u j + s * h j) (h j) t := by
      simpa using ((hasDerivAt_id t).mul_const (h j)).const_add (u j)
    exact h1.comp t h2
  have := HasDerivAt.fun_finsetProd hj
  unfold lind_D
  refine this.congr_deriv ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  have hsplit := (Finset.mul_prod_erase univ
    (fun i => iteratedDeriv ((o + (Pi.single l 1 : Fin d → ℕ)) i) (φ i) (u i + t * h i)) (mem_univ l)).symm
  have hrest : ∏ i ∈ univ.erase l, iteratedDeriv ((o + (Pi.single l 1 : Fin d → ℕ)) i) (φ i) (u i + t * h i)
      = ∏ i ∈ univ.erase l, iteratedDeriv (o i) (φ i) (u i + t * h i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (ne_of_mem_erase hi), add_zero]
  beta_reduce
  rw [hsplit, hrest, smul_eq_mul]
  simp only [Pi.add_apply, Pi.single_eq_same]
  ring

lemma lind_abs_D_le {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K) (o : Fin d → ℕ)
    (ho : ∀ j, o j ≤ 3) (x : Fin d → ℝ) : |lind_D φ o x| ≤ K ^ (∑ j, o j) := by
  unfold lind_D
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hφ.bound j (o j) (x j) (ho j))

lemma lind_abs_sum_mul_le (h A : Fin d → ℝ) (C : ℝ) (hA : ∀ l, |A l| ≤ C) :
    |∑ l, h l * A l| ≤ (∑ l, |h l|) * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hA l) (abs_nonneg _)

/-- **Taylor formula for products.** For admissible factors,
`f(u+h) = f(u) + L_u(h) + Q_u(h)/2 + R` with `|R| ≤ (K ‖h‖₁)³ / 6`. -/
theorem lind_taylor {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K) (u h : Fin d → ℝ) :
    |lind_F φ (u + h) - lind_F φ u - lind_lin φ u h - lind_quad φ u h / 2|
      ≤ (K * ∑ j, |h j|) ^ 3 / 6 := by
  classical
  set x : ℝ → Fin d → ℝ := fun t j => u j + t * h j with hx
  let g0 := fun t => lind_D φ 0 (x t)
  let g1 := fun t => ∑ l, h l * lind_D φ (0 + Pi.single l 1) (x t)
  let g2 := fun t => ∑ l, h l * ∑ k, h k * lind_D φ (0 + Pi.single l 1 + Pi.single k 1) (x t)
  let g3 := fun t => ∑ l, h l * ∑ k, h k * ∑ m, h m *
    lind_D φ (0 + Pi.single l 1 + Pi.single k 1 + Pi.single m 1) (x t)
  have d0 : ∀ t, HasDerivAt g0 (g1 t) t := fun t =>
    lind_hasDerivAt_D hφ.contDiff 0 (by simp) u h t
  have d1 : ∀ t, HasDerivAt g1 (g2 t) t := fun t =>
    HasDerivAt.fun_sum fun l _ => (lind_hasDerivAt_D hφ.contDiff _
      (fun j => by simp only [Pi.add_apply, Pi.zero_apply]; have := lind_single_le l j; omega)
      u h t).const_mul (h l)
  have d2 : ∀ t, HasDerivAt g2 (g3 t) t := fun t =>
    HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun k _ => (lind_hasDerivAt_D hφ.contDiff _
      (fun j => by
        simp only [Pi.add_apply, Pi.zero_apply]
        have := lind_single_le l j; have := lind_single_le k j; omega)
      u h t).const_mul (h k)).const_mul (h l)
  have hb : ∀ t, |g3 t| ≤ (K * ∑ j, |h j|) ^ 3 := by
    intro t
    have hD : ∀ l k m, |lind_D φ (0 + Pi.single l 1 + Pi.single k 1 + Pi.single m 1) (x t)|
        ≤ K ^ 3 := by
      intro l k m
      have := lind_abs_D_le hφ (0 + Pi.single l 1 + Pi.single k 1 + Pi.single m 1)
        (fun j => by
          simp only [Pi.add_apply, Pi.zero_apply]
          have := lind_single_le l j; have := lind_single_le k j; have := lind_single_le m j
          omega) (x t)
      simpa [Finset.sum_add_distrib, Finset.sum_pi_single'] using this
    have e := lind_abs_sum_mul_le h _ _ fun l =>
      lind_abs_sum_mul_le h _ _ fun k => lind_abs_sum_mul_le h _ _ fun m => hD l k m
    exact e.trans_eq (by ring)
  have := lind_taylor3 d0 d1 d2 (fun t _ => hb t)
  have e0 : g0 0 = lind_F φ u := by simp [g0, x, lind_D, lind_F]
  have e1 : g0 1 = lind_F φ (u + h) := by simp [g0, x, lind_D, lind_F]
  have e2 : g1 0 = lind_lin φ u h := by
    simp only [g1, x, lind_lin, zero_add, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e3 : g2 0 = lind_quad φ u h := by
    simp only [g2, x, lind_quad, lind_q, zero_add, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e0, e1, e2, e3] at this
  exact this

lemma lind_abs_q_le {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K) (u : Fin d → ℝ)
    (j k : Fin d) : |lind_q φ u j k| ≤ K ^ 2 := by
  have := lind_abs_D_le hφ (Pi.single j 1 + Pi.single k 1)
    (fun i => by
      simp only [Pi.add_apply]
      have := lind_single_le j i; have := lind_single_le k i; omega) u
  simpa [lind_q, Finset.sum_add_distrib, Finset.sum_pi_single'] using this

lemma lind_abs_F_le {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K) (x : Fin d → ℝ) :
    |lind_F φ x| ≤ 1 := by
  unfold lind_F
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun j _ => by
    simpa using hφ.bound j 0 (x j) (by norm_num)

lemma lind_continuous_F {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K) :
    Continuous (lind_F φ) := by
  unfold lind_F
  exact continuous_finsetProd _ fun j _ => (hφ.contDiff j).continuous.comp (continuous_apply j)

/-! ### Lindeberg replacement -/

lemma lind_integrable_of_abs_le_one {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {g : X → ℝ} (hg : Measurable g) (h1 : ∀ x, |g x| ≤ 1) :
    Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ fun x => by
    simpa [Real.norm_eq_abs] using h1 x)

lemma lind_sum_abs_nonneg (x : Fin d → ℝ) : 0 ≤ ∑ j, |x j| :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma lind_abs_le_sum_abs (x : Fin d → ℝ) (j : Fin d) : |x j| ≤ ∑ i, |x i| :=
  Finset.single_le_sum (f := fun i => |x i|) (fun _ _ => abs_nonneg _) (mem_univ j)

lemma lind_integrable_coord {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (h3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν) (j : Fin d) :
    Integrable (fun x => x j) ν := by
  refine Integrable.mono' ((integrable_const 1).add h3)
    (continuous_apply j).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hs := lind_abs_le_sum_abs x j
  have h0 := lind_sum_abs_nonneg x
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [mul_nonneg h0 (sq_nonneg (∑ i, |x i| - 1)), sq_nonneg (∑ i, |x i| - 1 / 2)]

lemma lind_integrable_mul {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (h3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν) (j k : Fin d) :
    Integrable (fun x => x j * x k) ν := by
  refine Integrable.mono' ((integrable_const 1).add h3)
    ((continuous_apply j).mul (continuous_apply k)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hj := lind_abs_le_sum_abs x j
  have hk := lind_abs_le_sum_abs x k
  have h0 := lind_sum_abs_nonneg x
  simp only [Real.norm_eq_abs, Pi.add_apply, abs_mul]
  have : |x j| * |x k| ≤ (∑ i, |x i|) ^ 2 := by
    rw [sq]; exact mul_le_mul hj hk (abs_nonneg _) h0
  nlinarith [mul_nonneg (sq_nonneg (∑ i, |x i| - 1)) (add_nonneg h0 zero_le_one)]

/-- Expansion of the expectation of a shifted product test function under a centred law. -/
lemma lind_integral_expand {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K)
    {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] (h0 : ∀ j, ∫ x, x j ∂μ = 0)
    (h3 : Integrable (fun x => (∑ j, |x j|) ^ 3) μ) (u : Fin d → ℝ) :
    ∫ y, lind_F φ (u + y) ∂μ = lind_F φ u
      + (∑ j, ∑ k, lind_q φ u j k * ∫ x, x j * x k ∂μ) / 2
      + ∫ y, (lind_F φ (u + y) - lind_F φ u - lind_lin φ u y - lind_quad φ u y / 2) ∂μ := by
  have hF : Integrable (fun y => lind_F φ (u + y)) μ :=
    lind_integrable_of_abs_le_one
      ((lind_continuous_F hφ).comp (continuous_const.add continuous_id)).measurable
      fun y => lind_abs_F_le hφ _
  have hL : Integrable (fun y => lind_lin φ u y) μ := by
    unfold lind_lin
    exact integrable_finsetSum _ fun j _ => (lind_integrable_coord h3 j).const_mul _
  have hQ : Integrable (fun y => lind_quad φ u y) μ := by
    unfold lind_quad
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (lind_integrable_mul h3 j k).const_mul _
  have iL : ∫ y, lind_lin φ u y ∂μ = 0 := by
    unfold lind_lin
    rw [integral_finsetSum _ fun j _ => (lind_integrable_coord h3 j).const_mul _]
    simp [integral_const_mul, h0]
  have iQ : ∫ y, lind_quad φ u y ∂μ = ∑ j, ∑ k, lind_q φ u j k * ∫ x, x j * x k ∂μ := by
    unfold lind_quad
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (lind_integrable_mul h3 j k).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => (lind_integrable_mul h3 j k).const_mul _]
    simp [integral_const_mul]
  rw [integral_sub (f := fun y => lind_F φ (u + y) - lind_F φ u - lind_lin φ u y)
      (g := fun y => lind_quad φ u y / 2) ((hF.sub (integrable_const _)).sub hL) (hQ.div_const 2),
    integral_sub (f := fun y => lind_F φ (u + y) - lind_F φ u) (g := fun y => lind_lin φ u y)
      (hF.sub (integrable_const _)) hL,
    integral_sub (f := fun y => lind_F φ (u + y)) (g := fun _ => lind_F φ u) hF
      (integrable_const _),
    integral_div, iL, iQ]
  simp

lemma lind_abs_integral_rem_le {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K)
    {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x => (∑ j, |x j|) ^ 3) μ) (u : Fin d → ℝ) :
    |∫ y, (lind_F φ (u + y) - lind_F φ u - lind_lin φ u y - lind_quad φ u y / 2) ∂μ|
      ≤ K ^ 3 / 6 * ∫ x, (∑ j, |x j|) ^ 3 ∂μ := by
  have hc : K ^ 3 / 6 * ∫ x, (∑ j, |x j|) ^ 3 ∂μ = ∫ x, K ^ 3 / 6 * (∑ j, |x j|) ^ 3 ∂μ :=
    (integral_const_mul _ _).symm
  rw [hc, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (h3.const_mul _) (ae_of_all _ fun y => ?_)
  have := lind_taylor hφ u y
  rw [Real.norm_eq_abs]
  exact this.trans_eq (by ring)

/-- **One Lindeberg swap.** Replacing a centred summand of law `ν` by one of law `γ` at an
arbitrary base point `u` changes the expectation of an admissible product test function by at most
the covariance mismatch times `K²/2` plus the third moments times `K³/6`. -/
theorem lind_step {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K)
    {ν γ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hν0 : ∀ j, ∫ x, x j ∂ν = 0) (hγ0 : ∀ j, ∫ x, x j ∂γ = 0)
    (hν3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν)
    (hγ3 : Integrable (fun x => (∑ j, |x j|) ^ 3) γ) (u : Fin d → ℝ) :
    |∫ y, lind_F φ (u + y) ∂ν - ∫ y, lind_F φ (u + y) ∂γ| ≤
      K ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂ν - ∫ x, x j * x k ∂γ| +
        K ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂ν + ∫ x, (∑ j, |x j|) ^ 3 ∂γ) := by
  rw [lind_integral_expand hφ hν0 hν3 u, lind_integral_expand hφ hγ0 hγ3 u]
  have hRν := lind_abs_integral_rem_le hφ hν3 u
  have hRγ := lind_abs_integral_rem_le hφ hγ3 u
  have hQ : |∑ j, ∑ k, lind_q φ u j k * ∫ x, x j * x k ∂ν
      - ∑ j, ∑ k, lind_q φ u j k * ∫ x, x j * x k ∂γ|
      ≤ K ^ 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂ν - ∫ x, x j * x k ∂γ| := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (lind_abs_q_le hφ u j k) (abs_nonneg _)
  have key : ∀ a b c e f : ℝ, |a + b / 2 + c - (a + e / 2 + f)| ≤ |b - e| / 2 + |c| + |f| := by
    intro a b c e f
    have : a + b / 2 + c - (a + e / 2 + f) = (b - e) / 2 + c - f := by ring
    rw [this]
    calc |(b - e) / 2 + c - f| = |(b - e) / 2 + c + (-f)| := by rw [sub_eq_add_neg]
      _ ≤ |(b - e) / 2| + |c| + |-f| := abs_add_three _ _ _
      _ = |b - e| / 2 + |c| + |f| := by rw [abs_neg, abs_div, abs_two]
  refine (key _ _ _ _ _).trans ?_
  nlinarith [hQ, hRν, hRγ]

lemma lind_integral_pi_succ {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    {G : (Fin d → ℝ) → ℝ} (hG : Continuous G) (hG1 : ∀ x, |G x| ≤ 1) (B : ℕ) :
    ∫ x, G (∑ β, x β) ∂(Measure.pi fun _ : Fin (B + 1) => μ)
      = ∫ a, ∫ b, G (a + ∑ β, b β) ∂(Measure.pi fun _ : Fin B => μ) ∂μ := by
  have e := (measurePreserving_piFinSuccAbove (fun _ : Fin (B + 1) => μ) 0).symm
  rw [← e.integral_comp' (fun x => G (∑ β, x β))]
  rw [integral_prod]
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero',
      Fin.sum_univ_succ]
  · refine lind_integrable_of_abs_le_one ?_ fun p => hG1 _
    exact hG.measurable.comp ((Finset.measurable_sum _ fun β _ => measurable_pi_apply β).comp
      (MeasurableEquiv.measurable _))

lemma lind_integrable_uncurry {B : ℕ} {F : (Fin d → ℝ) → ℝ} (hF : Continuous F)
    (hF1 : ∀ x, |F x| ≤ 1) (v : Fin d → ℝ) (μ1 : Measure (Fin d → ℝ)) [IsFiniteMeasure μ1]
    (μ2 : Measure (Fin B → Fin d → ℝ)) [IsFiniteMeasure μ2] :
    Integrable (Function.uncurry fun a (b : Fin B → Fin d → ℝ) => F (v + (a + ∑ β, b β)))
      (μ1.prod μ2) := by
  refine lind_integrable_of_abs_le_one ?_ fun p => hF1 _
  have : Continuous fun p : (Fin d → ℝ) × (Fin B → Fin d → ℝ) => F (v + (p.1 + ∑ β, p.2 β)) := by
    fun_prop
  exact this.measurable

/-- **Lindeberg telescoping.** If one swap of a summand costs at most `E` at every base point,
then replacing all `B` iid summands costs at most `B * E`. -/
theorem lind_pi_of_step {F : (Fin d → ℝ) → ℝ} (hF : Continuous F) (hF1 : ∀ x, |F x| ≤ 1)
    {ν γ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] [IsProbabilityMeasure γ] {E : ℝ}
    (hstep : ∀ u, |∫ y, F (u + y) ∂ν - ∫ y, F (u + y) ∂γ| ≤ E) (B : ℕ) (v : Fin d → ℝ) :
    |∫ x, F (v + ∑ β, x β) ∂(Measure.pi fun _ : Fin B => ν)
      - ∫ x, F (v + ∑ β, x β) ∂(Measure.pi fun _ : Fin B => γ)| ≤ B * E := by
  induction B generalizing v with
  | zero => simp
  | succ B ih =>
    have hG : Continuous fun s => F (v + s) := hF.comp (continuous_const.add continuous_id)
    rw [lind_integral_pi_succ (μ := ν) (G := fun s => F (v + s)) hG (fun s => hF1 _) B,
      lind_integral_pi_succ (μ := γ) (G := fun s => F (v + s)) hG (fun s => hF1 _) B]
    set ρν := Measure.pi fun _ : Fin B => ν
    set ργ := Measure.pi fun _ : Fin B => γ
    have hswap : ∀ (μ1 : Measure (Fin d → ℝ)) [IsFiniteMeasure μ1]
        (μ2 : Measure (Fin B → Fin d → ℝ)) [IsFiniteMeasure μ2],
        ∫ a, ∫ b, F (v + (a + ∑ β, b β)) ∂μ2 ∂μ1 = ∫ b, ∫ a, F (v + (a + ∑ β, b β)) ∂μ1 ∂μ2 :=
      fun μ1 _ μ2 _ => integral_integral_swap (lind_integrable_uncurry hF hF1 v μ1 μ2)
    have hIl : ∀ (μ1 : Measure (Fin d → ℝ)) [IsFiniteMeasure μ1]
        (μ2 : Measure (Fin B → Fin d → ℝ)) [IsFiniteMeasure μ2],
        Integrable (fun a => ∫ b, F (v + (a + ∑ β, b β)) ∂μ2) μ1 :=
      fun μ1 _ μ2 _ => (lind_integrable_uncurry hF hF1 v μ1 μ2).integral_prod_left
    have hIr : ∀ (μ1 : Measure (Fin d → ℝ)) [IsFiniteMeasure μ1]
        (μ2 : Measure (Fin B → Fin d → ℝ)) [IsFiniteMeasure μ2],
        Integrable (fun b => ∫ a, F (v + (a + ∑ β, b β)) ∂μ1) μ2 :=
      fun μ1 _ μ2 _ => (lind_integrable_uncurry hF hF1 v μ1 μ2).integral_prod_right
    have h1 : |∫ a, ∫ b, F (v + (a + ∑ β, b β)) ∂ρν ∂ν
        - ∫ a, ∫ b, F (v + (a + ∑ β, b β)) ∂ρν ∂γ| ≤ E := by
      rw [hswap ν ρν, hswap γ ρν, ← integral_sub (hIr ν ρν) (hIr γ ρν), ← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := E) (ae_of_all _ fun b => ?_)).trans (by simp)
      rw [Real.norm_eq_abs]
      have hc : ∀ a, v + (a + ∑ β, b β) = (v + ∑ β, b β) + a := fun a => by abel
      simp only [hc]
      exact hstep _
    have h2 : |∫ a, ∫ b, F (v + (a + ∑ β, b β)) ∂ρν ∂γ
        - ∫ a, ∫ b, F (v + (a + ∑ β, b β)) ∂ργ ∂γ| ≤ B * E := by
      rw [← integral_sub (hIl γ ρν) (hIl γ ργ), ← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := B * E) (ae_of_all _ fun a => ?_)).trans
        (by simp)
      rw [Real.norm_eq_abs]
      have hc : ∀ b : Fin B → Fin d → ℝ, v + (a + ∑ β, b β) = (v + a) + ∑ β, b β :=
        fun b => by abel
      simp only [hc]
      exact ih (v + a)
    calc _ ≤ _ := abs_sub_le _ (∫ a, ∫ b, F (v + (a + ∑ β, b β)) ∂ρν ∂γ) _
      _ ≤ E + B * E := add_le_add h1 h2
      _ = ((B + 1 : ℕ) : ℝ) * E := by push_cast; ring

/-- **Lindeberg's replacement bound**, iid form with a base point `v`. -/
theorem lind_pi_shift {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K)
    {ν γ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hν0 : ∀ j, ∫ x, x j ∂ν = 0) (hγ0 : ∀ j, ∫ x, x j ∂γ = 0)
    (hν3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν)
    (hγ3 : Integrable (fun x => (∑ j, |x j|) ^ 3) γ) (B : ℕ) (v : Fin d → ℝ) :
    |∫ x, lind_F φ (v + ∑ β, x β) ∂(Measure.pi fun _ : Fin B => ν)
      - ∫ x, lind_F φ (v + ∑ β, x β) ∂(Measure.pi fun _ : Fin B => γ)| ≤
      B * (K ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂ν - ∫ x, x j * x k ∂γ| +
        K ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂ν + ∫ x, (∑ j, |x j|) ^ 3 ∂γ)) :=
  lind_pi_of_step (lind_continuous_F hφ) (lind_abs_F_le hφ)
    (lind_step hφ hν0 hγ0 hν3 hγ3) B v

/-- **Lindeberg's replacement bound**, iid form: for an admissible product test function `f`,
`|E f(Σ_β X_β) - E f(Σ_β G_β)| ≤ B (K²/2 Σ_{j,k} |cov mismatch| + K³/6 (third moments))`, where
the `X_β` are iid of law `ν`, the `G_β` iid of law `γ`, both centred. -/
theorem lind_pi {φ : Fin d → ℝ → ℝ} {K : ℝ} (hφ : LindFactors φ K)
    {ν γ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hν0 : ∀ j, ∫ x, x j ∂ν = 0) (hγ0 : ∀ j, ∫ x, x j ∂γ = 0)
    (hν3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν)
    (hγ3 : Integrable (fun x => (∑ j, |x j|) ^ 3) γ) (B : ℕ) :
    |∫ x, lind_F φ (∑ β, x β) ∂(Measure.pi fun _ : Fin B => ν)
      - ∫ x, lind_F φ (∑ β, x β) ∂(Measure.pi fun _ : Fin B => γ)| ≤
      B * (K ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂ν - ∫ x, x j * x k ∂γ| +
        K ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂ν + ∫ x, (∑ j, |x j|) ^ 3 ∂γ)) := by
  simpa using lind_pi_shift hφ hν0 hγ0 hν3 hγ3 B 0

/-! ### The cut-off function `ψ` -/

/-- `ψ = 1 - smoothTransition`: smooth, `1` on `(-∞, 0]`, `0` on `[1, ∞)`, values in `[0,1]`. -/
def lind_psi (t : ℝ) : ℝ := 1 - Real.smoothTransition t

lemma lind_psi_nonneg (t : ℝ) : 0 ≤ lind_psi t :=
  sub_nonneg.2 (Real.smoothTransition.le_one t)

lemma lind_psi_le_one (t : ℝ) : lind_psi t ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg t)

lemma lind_psi_of_nonpos {t : ℝ} (ht : t ≤ 0) : lind_psi t = 1 := by
  simp [lind_psi, Real.smoothTransition.zero_of_nonpos ht]

lemma lind_psi_of_one_le {t : ℝ} (ht : 1 ≤ t) : lind_psi t = 0 := by
  simp [lind_psi, Real.smoothTransition.one_of_one_le ht]

lemma lind_psi_contDiff {n : ℕ∞} : ContDiff ℝ n lind_psi :=
  contDiff_const.sub Real.smoothTransition.contDiff

lemma lind_psi_contDiff_nat (n : ℕ) : ContDiff ℝ n lind_psi := by
  exact_mod_cast lind_psi_contDiff (n := n)

lemma lind_psi_continuous : Continuous lind_psi :=
  (lind_psi_contDiff_nat 0).continuous

lemma lind_iteratedDeriv_psi_eq_zero {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    iteratedDeriv n lind_psi t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · have h : lind_psi =ᶠ[𝓝 t] fun _ => 1 :=
      Filter.eventually_of_mem (Iio_mem_nhds ht) fun s hs => lind_psi_of_nonpos (le_of_lt hs)
    rw [h.iteratedDeriv_eq, iteratedDeriv_const]; simp [hn]
  · have h : lind_psi =ᶠ[𝓝 t] fun _ => 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => lind_psi_of_one_le (le_of_lt hs)
    rw [h.iteratedDeriv_eq, iteratedDeriv_const]; simp [hn]

lemma lind_abs_psi_le_one (t : ℝ) : |lind_psi t| ≤ 1 :=
  abs_le.2 ⟨by linarith [lind_psi_nonneg t], lind_psi_le_one t⟩

lemma lind_exists_Kpsi :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n ≤ 3, ∀ t, |iteratedDeriv n lind_psi t| ≤ K ^ n := by
  have hb : ∀ n : ℕ, ∃ C, ∀ t, |iteratedDeriv n lind_psi t| ≤ C := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun t => by rw [iteratedDeriv_zero]; exact lind_abs_psi_le_one t⟩
    · obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        ((lind_psi_contDiff_nat n).continuous_iteratedDeriv' n).continuousOn
      refine ⟨max C 0, fun t => ?_⟩
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · have := hC t ht
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      · rw [lind_iteratedDeriv_psi_eq_zero hn.ne' ht, abs_zero]; exact le_max_right _ _
  choose C hC using hb
  refine ⟨max 1 (max (C 1) (max (C 2) (C 3))), le_max_left _ _, fun n hn t => ?_⟩
  have hK1 : (1 : ℝ) ≤ max 1 (max (C 1) (max (C 2) (C 3))) := le_max_left _ _
  interval_cases n
  · rw [iteratedDeriv_zero, pow_zero]; exact lind_abs_psi_le_one t
  · rw [pow_one]
    exact (hC 1 t).trans (le_max_of_le_right (le_max_left _ _))
  · exact (hC 2 t).trans ((le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans
      (le_self_pow₀ hK1 (by norm_num)))
  · exact (hC 3 t).trans ((le_max_of_le_right (le_max_of_le_right (le_max_right _ _))).trans
      (le_self_pow₀ hK1 (by norm_num)))

/-- A constant `Kψ ≥ 1` with `|ψ^(n)| ≤ Kψ ^ n` on `ℝ` for `n ≤ 3`. -/
def lind_Kpsi : ℝ := Classical.choose lind_exists_Kpsi

lemma one_le_lind_Kpsi : 1 ≤ lind_Kpsi := (Classical.choose_spec lind_exists_Kpsi).1

lemma lind_Kpsi_pos : 0 < lind_Kpsi := zero_lt_one.trans_le one_le_lind_Kpsi

lemma lind_abs_iteratedDeriv_psi_le {n : ℕ} (hn : n ≤ 3) (t : ℝ) :
    |iteratedDeriv n lind_psi t| ≤ lind_Kpsi ^ n :=
  (Classical.choose_spec lind_exists_Kpsi).2 n hn t

/-- The rescaled cut-offs `t ↦ ψ((t - c j)/ε + b)` are admissible factors with `K = Kψ/ε`. -/
lemma lind_factors_psi (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (b : ℝ) :
    LindFactors (fun j t => lind_psi ((t - c j) / ε + b)) (lind_Kpsi / ε) where
  nonneg := div_nonneg lind_Kpsi_pos.le hε.le
  contDiff j := (lind_psi_contDiff_nat 3).comp
    (((contDiff_id.sub contDiff_const).div_const _).add contDiff_const)
  bound j n t hn := by
    have hfun : (fun t => lind_psi ((t - c j) / ε + b))
        = fun t => (fun s => lind_psi (s + (b - c j / ε))) (ε⁻¹ * t) := by
      funext t; beta_reduce; congr 1; ring
    have hcd : ContDiff ℝ n (fun s => lind_psi (s + (b - c j / ε))) :=
      (lind_psi_contDiff_nat n).comp (contDiff_id.add contDiff_const)
    rw [hfun, iteratedDeriv_comp_const_mul hcd, iteratedDeriv_comp_add_const]
    calc |ε⁻¹ ^ n * iteratedDeriv n lind_psi (ε⁻¹ * t + (b - c j / ε))|
        = ε⁻¹ ^ n * |iteratedDeriv n lind_psi (ε⁻¹ * t + (b - c j / ε))| := by
          rw [abs_mul, abs_pow, abs_inv, abs_of_pos hε]
      _ ≤ ε⁻¹ ^ n * lind_Kpsi ^ n :=
          mul_le_mul_of_nonneg_left (lind_abs_iteratedDeriv_psi_le hn _) (by positivity)
      _ = (lind_Kpsi / ε) ^ n := by rw [div_eq_mul_inv, mul_pow, mul_comm]

/-! ### Smooth orthant functions -/

/-- Smooth upper orthant function: `1` on `{x ≤ c}`, `0` off `{x ≤ c + ε}`. -/
def orthUp (c : Fin d → ℝ) (ε : ℝ) (x : Fin d → ℝ) : ℝ := ∏ j, lind_psi ((x j - c j) / ε)

/-- Smooth lower orthant function: `1` on `{x ≤ c - ε}`, `0` off `{x ≤ c}`. -/
def orthLow (c : Fin d → ℝ) (ε : ℝ) (x : Fin d → ℝ) : ℝ := ∏ j, lind_psi ((x j - c j) / ε + 1)

lemma orthUp_eq_lind_F (c : Fin d → ℝ) (ε : ℝ) :
    orthUp c ε = lind_F (fun j t => lind_psi ((t - c j) / ε + 0)) := by
  funext x; simp [orthUp, lind_F]

lemma orthLow_eq_lind_F (c : Fin d → ℝ) (ε : ℝ) :
    orthLow c ε = lind_F (fun j t => lind_psi ((t - c j) / ε + 1)) := rfl

lemma orthUp_nonneg (c : Fin d → ℝ) (ε : ℝ) (x : Fin d → ℝ) : 0 ≤ orthUp c ε x :=
  Finset.prod_nonneg fun _ _ => lind_psi_nonneg _

lemma orthUp_le_one (c : Fin d → ℝ) (ε : ℝ) (x : Fin d → ℝ) : orthUp c ε x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => lind_psi_nonneg _) fun _ _ => lind_psi_le_one _

lemma orthLow_nonneg (c : Fin d → ℝ) (ε : ℝ) (x : Fin d → ℝ) : 0 ≤ orthLow c ε x :=
  Finset.prod_nonneg fun _ _ => lind_psi_nonneg _

lemma orthLow_le_one (c : Fin d → ℝ) (ε : ℝ) (x : Fin d → ℝ) : orthLow c ε x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => lind_psi_nonneg _) fun _ _ => lind_psi_le_one _

lemma continuous_orthUp (c : Fin d → ℝ) (ε : ℝ) : Continuous (orthUp c ε) := by
  unfold orthUp
  exact continuous_finsetProd _ fun j _ => lind_psi_continuous.comp
    (((continuous_apply j).sub continuous_const).div_const _)

lemma continuous_orthLow (c : Fin d → ℝ) (ε : ℝ) : Continuous (orthLow c ε) := by
  unfold orthLow
  exact continuous_finsetProd _ fun j _ => lind_psi_continuous.comp
    ((((continuous_apply j).sub continuous_const).div_const _).add continuous_const)

lemma measurable_orthUp (c : Fin d → ℝ) (ε : ℝ) : Measurable (orthUp c ε) :=
  (continuous_orthUp c ε).measurable

lemma measurable_orthLow (c : Fin d → ℝ) (ε : ℝ) : Measurable (orthLow c ε) :=
  (continuous_orthLow c ε).measurable

lemma orthUp_eq_one {c : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (h : ∀ j, x j ≤ c j) : orthUp c ε x = 1 :=
  Finset.prod_eq_one fun j _ =>
    lind_psi_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (h j)) hε.le)

lemma orthUp_eq_zero {c : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (h : ¬ ∀ j, x j ≤ c j + ε) : orthUp c ε x = 0 := by
  obtain ⟨j, hj⟩ := not_forall.1 h
  rw [not_le] at hj
  exact Finset.prod_eq_zero (mem_univ j) (lind_psi_of_one_le (by rw [le_div_iff₀ hε]; linarith))

lemma orthLow_eq_one {c : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (h : ∀ j, x j ≤ c j - ε) : orthLow c ε x = 1 :=
  Finset.prod_eq_one fun j _ => lind_psi_of_nonpos (by
    have : (x j - c j) / ε ≤ -1 := by rw [div_le_iff₀ hε]; linarith [h j]
    linarith)

lemma orthLow_eq_zero {c : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (h : ¬ ∀ j, x j ≤ c j) : orthLow c ε x = 0 := by
  obtain ⟨j, hj⟩ := not_forall.1 h
  rw [not_le] at hj
  exact Finset.prod_eq_zero (mem_univ j) (lind_psi_of_one_le (by
    have : 0 < (x j - c j) / ε := div_pos (by linarith) hε
    linarith))

/-- The sandwich `1{x ≤ c - ε} ≤ orthLow ≤ 1{x ≤ c} ≤ orthUp ≤ 1{x ≤ c + ε}`, first link. -/
lemma indicator_le_orthLow (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    {x : Fin d → ℝ | ∀ j, x j ≤ c j - ε}.indicator 1 x ≤ orthLow c ε x := by
  by_cases h : ∀ j, x j ≤ c j - ε
  · rw [indicator_of_mem (show x ∈ {x : Fin d → ℝ | ∀ j, x j ≤ c j - ε} from h),
      orthLow_eq_one hε h, Pi.one_apply]
  · rw [indicator_of_notMem (show x ∉ {x : Fin d → ℝ | ∀ j, x j ≤ c j - ε} from h)]
    exact orthLow_nonneg c ε x

/-- The sandwich, second link. -/
lemma orthLow_le_indicator (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    orthLow c ε x ≤ {x : Fin d → ℝ | ∀ j, x j ≤ c j}.indicator 1 x := by
  by_cases h : ∀ j, x j ≤ c j
  · rw [indicator_of_mem (show x ∈ {x : Fin d → ℝ | ∀ j, x j ≤ c j} from h), Pi.one_apply]
    exact orthLow_le_one c ε x
  · rw [indicator_of_notMem (show x ∉ {x : Fin d → ℝ | ∀ j, x j ≤ c j} from h),
      orthLow_eq_zero hε h]

/-- The sandwich, third link. -/
lemma indicator_le_orthUp (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    {x : Fin d → ℝ | ∀ j, x j ≤ c j}.indicator 1 x ≤ orthUp c ε x := by
  by_cases h : ∀ j, x j ≤ c j
  · rw [indicator_of_mem (show x ∈ {x : Fin d → ℝ | ∀ j, x j ≤ c j} from h),
      orthUp_eq_one hε h, Pi.one_apply]
  · rw [indicator_of_notMem (show x ∉ {x : Fin d → ℝ | ∀ j, x j ≤ c j} from h)]
    exact orthUp_nonneg c ε x

/-- The sandwich, fourth link. -/
lemma orthUp_le_indicator (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    orthUp c ε x ≤ {x : Fin d → ℝ | ∀ j, x j ≤ c j + ε}.indicator 1 x := by
  by_cases h : ∀ j, x j ≤ c j + ε
  · rw [indicator_of_mem (show x ∈ {x : Fin d → ℝ | ∀ j, x j ≤ c j + ε} from h), Pi.one_apply]
    exact orthUp_le_one c ε x
  · rw [indicator_of_notMem (show x ∉ {x : Fin d → ℝ | ∀ j, x j ≤ c j + ε} from h),
      orthUp_eq_zero hε h]

/-! ### The sandwich in expectation -/

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {g : Ω → Fin d → ℝ}

lemma lind_measurableSet_orth (hg : Measurable g) (a : Fin d → ℝ) :
    MeasurableSet {ω | ∀ j, g ω j ≤ a j} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le ((measurable_pi_apply j).comp hg) measurable_const

omit [IsFiniteMeasure μ] in
lemma lind_integral_indicator_orth (hg : Measurable g) (a : Fin d → ℝ) :
    ∫ ω, {x : Fin d → ℝ | ∀ j, x j ≤ a j}.indicator 1 (g ω) ∂μ
      = μ.real {ω | ∀ j, g ω j ≤ a j} := by
  rw [← integral_indicator_one (lind_measurableSet_orth hg a)]
  rfl

lemma lind_integrable_indicator_orth (hg : Measurable g) (a : Fin d → ℝ) :
    Integrable (fun ω => {x : Fin d → ℝ | ∀ j, x j ≤ a j}.indicator (1 : (Fin d → ℝ) → ℝ) (g ω))
      μ :=
  (integrable_const (1 : ℝ)).indicator (lind_measurableSet_orth hg a)

lemma lind_integrable_orthUp (hg : Measurable g) (c : Fin d → ℝ) (ε : ℝ) :
    Integrable (fun ω => orthUp c ε (g ω)) μ :=
  lind_integrable_of_abs_le_one ((measurable_orthUp c ε).comp hg) fun ω =>
    abs_le.2 ⟨by linarith [orthUp_nonneg c ε (g ω)], orthUp_le_one c ε (g ω)⟩

lemma lind_integrable_orthLow (hg : Measurable g) (c : Fin d → ℝ) (ε : ℝ) :
    Integrable (fun ω => orthLow c ε (g ω)) μ :=
  lind_integrable_of_abs_le_one ((measurable_orthLow c ε).comp hg) fun ω =>
    abs_le.2 ⟨by linarith [orthLow_nonneg c ε (g ω)], orthLow_le_one c ε (g ω)⟩

/-- `P(g ≤ c - ε) ≤ E orthLow(g)`. -/
lemma lind_real_le_integral_orthLow (hg : Measurable g) (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∀ j, g ω j ≤ c j - ε} ≤ ∫ ω, orthLow c ε (g ω) ∂μ := by
  rw [← lind_integral_indicator_orth hg (fun j => c j - ε)]
  exact integral_mono (lind_integrable_indicator_orth hg _) (lind_integrable_orthLow hg c ε)
    fun ω => indicator_le_orthLow c hε (g ω)

/-- `E orthLow(g) ≤ P(g ≤ c)`. -/
lemma lind_integral_orthLow_le (hg : Measurable g) (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, orthLow c ε (g ω) ∂μ ≤ μ.real {ω | ∀ j, g ω j ≤ c j} := by
  rw [← lind_integral_indicator_orth hg c]
  exact integral_mono (lind_integrable_orthLow hg c ε) (lind_integrable_indicator_orth hg _)
    fun ω => orthLow_le_indicator c hε (g ω)

/-- `P(g ≤ c) ≤ E orthUp(g)`. -/
lemma lind_real_le_integral_orthUp (hg : Measurable g) (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∀ j, g ω j ≤ c j} ≤ ∫ ω, orthUp c ε (g ω) ∂μ := by
  rw [← lind_integral_indicator_orth hg c]
  exact integral_mono (lind_integrable_indicator_orth hg _) (lind_integrable_orthUp hg c ε)
    fun ω => indicator_le_orthUp c hε (g ω)

/-- `E orthUp(g) ≤ P(g ≤ c + ε)`. -/
lemma lind_integral_orthUp_le (hg : Measurable g) (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, orthUp c ε (g ω) ∂μ ≤ μ.real {ω | ∀ j, g ω j ≤ c j + ε} := by
  rw [← lind_integral_indicator_orth hg (fun j => c j + ε)]
  exact integral_mono (lind_integrable_orthUp hg c ε) (lind_integrable_indicator_orth hg _)
    fun ω => orthUp_le_indicator c hε (g ω)

end Expect

/-! ### Lindeberg bounds for the orthant functions -/

/-- Lindeberg bound for the smooth upper orthant function (`K = Kψ/ε`). -/
theorem lind_orthUp_pi {ν γ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    (hν0 : ∀ j, ∫ x, x j ∂ν = 0) (hγ0 : ∀ j, ∫ x, x j ∂γ = 0)
    (hν3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν)
    (hγ3 : Integrable (fun x => (∑ j, |x j|) ^ 3) γ)
    (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    |∫ x, orthUp c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin B => ν)
      - ∫ x, orthUp c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin B => γ)| ≤
      B * ((lind_Kpsi / ε) ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂ν - ∫ x, x j * x k ∂γ| +
        (lind_Kpsi / ε) ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂ν + ∫ x, (∑ j, |x j|) ^ 3 ∂γ)) := by
  rw [orthUp_eq_lind_F]
  exact lind_pi (lind_factors_psi c hε 0) hν0 hγ0 hν3 hγ3 B

/-- Lindeberg bound for the smooth lower orthant function (`K = Kψ/ε`). -/
theorem lind_orthLow_pi {ν γ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    (hν0 : ∀ j, ∫ x, x j ∂ν = 0) (hγ0 : ∀ j, ∫ x, x j ∂γ = 0)
    (hν3 : Integrable (fun x => (∑ j, |x j|) ^ 3) ν)
    (hγ3 : Integrable (fun x => (∑ j, |x j|) ^ 3) γ)
    (c : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    |∫ x, orthLow c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin B => ν)
      - ∫ x, orthLow c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin B => γ)| ≤
      B * ((lind_Kpsi / ε) ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂ν - ∫ x, x j * x k ∂γ| +
        (lind_Kpsi / ε) ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂ν + ∫ x, (∑ j, |x j|) ^ 3 ∂γ)) := by
  rw [orthLow_eq_lind_F]
  exact lind_pi (lind_factors_psi c hε 1) hν0 hγ0 hν3 hγ3 B

end

end Census
end IIT
