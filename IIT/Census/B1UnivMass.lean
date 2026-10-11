/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: the generic-mass fields `low` and `upTe` of `UnivGood`
given the fixed rows.

A generic row `r` sends the system to the pattern `t` with probability `RP s t (g r) = ∏_k rp s t k (g r k)`,
a product of `N` independent readings, each `clamp01` or `1 - clamp01` of a uniform entry:
`E RP = 2^{-N}`, `E RP² = 3^{-N}`.
* `low_one` (Chernoff, lower tail, `e^{-u} ≤ 1 - u + u²/2`): `P(Σ_r RP < 1/2) ≤ e^{-(3/2)^N/32}`;
  a union over the `2^N` patterns gives `low_cond`.
* `up_one` (Chebyshev): `P(Σ_r RP > 3/2) ≤ 4 (2/3)^N`; at `t = teW` (a function of the fixed row `s`)
  this is `upTe_cond`.
-/
import IIT.Census.B1UnivConc

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

variable {N : ℕ}

/-! ### One reading -/

/-- The reading of entry `k` of a generic row towards pattern `t`. -/
noncomputable def rp (s t : State N) (k : Fin N) (v : ℝ) : ℝ :=
  if t k then clamp01 (flipC (s k) v) else 1 - clamp01 (flipC (s k) v)

lemma rp_cases (s t : State N) (k : Fin N) :
    (∀ v, rp s t k v = clamp01 v) ∨ (∀ v, rp s t k v = 1 - clamp01 v) := by
  unfold rp flipC
  cases t k <;> cases s k <;> simp [clamp01_one_sub]

lemma rp_mem (s t : State N) (k : Fin N) (v : ℝ) : rp s t k v ∈ Set.Icc (0 : ℝ) 1 := by
  rcases rp_cases s t k with h | h <;> rw [h v]
  · exact ⟨clamp01_nonneg v, clamp01_le_one v⟩
  · exact ⟨by linarith [clamp01_le_one v], by linarith [clamp01_nonneg v]⟩

lemma rp_meas (s t : State N) (k : Fin N) : Measurable (rp s t k) := by
  rcases rp_cases s t k with h | h
  · rw [funext h]; exact clamp01_measurable
  · rw [funext h]; exact measurable_const.sub clamp01_measurable

lemma integrable_of_mem01 {f : ℝ → ℝ} (hm : Measurable f) (h : ∀ v, f v ∈ Set.Icc (0 : ℝ) 1) :
    Integrable f unif :=
  Integrable.of_bound hm.aestronglyMeasurable 1
    (ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (h v).1]; exact (h v).2)

lemma rp_int (s t : State N) (k : Fin N) : ∫ v, rp s t k v ∂unif = 1 / 2 := by
  rcases rp_cases s t k with h | h <;> simp_rw [h]
  · exact integral_clamp
  · exact integral_one_sub_clamp

lemma rp_int_sq (s t : State N) (k : Fin N) : ∫ v, rp s t k v ^ 2 ∂unif = 1 / 3 := by
  have h2 := integral_cl_pow 2
  norm_num at h2
  have hi : Integrable clamp01 unif :=
    integrable_of_mem01 clamp01_measurable fun v => ⟨clamp01_nonneg v, clamp01_le_one v⟩
  have hi2 : Integrable (fun v => clamp01 v ^ 2) unif :=
    integrable_of_mem01 (clamp01_measurable.pow_const 2) fun v =>
      ⟨sq_nonneg _, by nlinarith [clamp01_nonneg v, clamp01_le_one v]⟩
  rcases rp_cases s t k with h | h <;> simp_rw [h]
  · exact h2
  · have e : ∀ v, (1 - clamp01 v) ^ 2 = 1 - 2 * clamp01 v + clamp01 v ^ 2 := fun v => by ring
    simp_rw [e]
    have hA : Integrable (fun v => 1 - 2 * clamp01 v) unif := (integrable_const 1).sub (hi.const_mul 2)
    have e1 := integral_add hA hi2
    have e2 := integral_sub (integrable_const (1 : ℝ)) (hi.const_mul 2) (μ := unif)
    rw [e1, e2, integral_const_mul, integral_clamp, h2, integral_const]
    norm_num

/-! ### One generic row -/

/-- The probability that a generic row (entries `v`) sends the system to `t`. -/
noncomputable def RP (s t : State N) (v : Fin N → ℝ) : ℝ := ∏ k, rp s t k (v k)

lemma RP_mem (s t : State N) (v : Fin N → ℝ) : RP s t v ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨prod_nonneg fun k _ => (rp_mem s t k _).1, prod_le_one (fun k _ => (rp_mem s t k _).1)
    fun k _ => (rp_mem s t k _).2⟩

lemma RP_meas (s t : State N) : Measurable (RP s t) := by
  unfold RP
  exact Finset.measurable_prod _ fun k _ => (rp_meas s t k).comp (measurable_pi_apply k)

lemma RP_int (s t : State N) : ∫ v, RP s t v ∂rowM N = (1 / 2) ^ N := by
  unfold RP rowM
  rw [integral_fintype_prod_eq_prod (fun k v => rp s t k v)]
  simp [rp_int]

lemma RP_int_sq (s t : State N) : ∫ v, RP s t v ^ 2 ∂rowM N = (1 / 3) ^ N := by
  unfold RP rowM
  simp_rw [← prod_pow]
  rw [integral_fintype_prod_eq_prod (fun k v => rp s t k v ^ 2)]
  simp [rp_int_sq]

/-- A generic row of the glued parameter. -/
lemma fullProb_glue (A : Finset (State N)) (s : State N) (f : A → Fin N → ℝ)
    (g : {r // r ∉ A} → Fin N → ℝ) {r : State N} (hr : r ∉ A) (t : State N) :
    fullProb (tpmOf (flipP s (glueRows A f g))) r t = RP s t (g ⟨r, hr⟩) := by
  unfold fullProb RP
  refine prod_congr rfl fun k _ => ?_
  simp only [rp, tpmOf, flipP, glueRows_of_not_mem A f g hr]

lemma sum_compl_glue (A : Finset (State N)) (s : State N) (f : A → Fin N → ℝ)
    (g : {r // r ∉ A} → Fin N → ℝ) (t : State N) :
    ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s (glueRows A f g))) r t = ∑ r : {r // r ∉ A}, RP s t (g r) := by
  rw [sum_subtype (p := fun r => r ∉ A) Aᶜ (fun r => by simp)]
  exact sum_congr rfl fun r _ => fullProb_glue A s f g r.2 t

lemma card_generic (A : Finset (State N)) :
    (Fintype.card {r // r ∉ A} : ℝ) = 2 ^ N - A.card := by
  have h1 : Fintype.card {r // r ∉ A} = Aᶜ.card := by
    rw [Fintype.card_subtype]; congr 1; ext r; simp
  have h2 : Aᶜ.card + A.card = 2 ^ N := by
    rw [card_compl]; simp only [Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
    have := card_le_univ A
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    omega
  rw [h1]
  have : ((Aᶜ.card : ℕ) : ℝ) + A.card = 2 ^ N := by exact_mod_cast h2
  linarith

/-! ### Lower tail (Chernoff) -/

lemma exp_neg_le_quad {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have h := Real.sum_le_exp_of_nonneg hu 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  have hb : 0 < 1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by positivity
  have hab : 1 ≤ (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) := by
    nlinarith [pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5]
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos u)]
  have ha : 0 ≤ 1 - u + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1)]
  calc (1 : ℝ) ≤ (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) := hab
    _ ≤ (1 - u + u ^ 2 / 2) * Real.exp u := by
        apply mul_le_mul_of_nonneg_left _ ha
        linarith

/-- `E e^{-λ RP} ≤ exp(-λ 2^{-N} + λ² 3^{-N}/2)`. -/
lemma RP_mgf_neg (s t : State N) {l : ℝ} (hl : 0 ≤ l) :
    ∫ v, Real.exp (-(l * RP s t v)) ∂rowM N ≤
      Real.exp (-(l * (1 / 2) ^ N) + l ^ 2 * (1 / 3) ^ N / 2) := by
  have hm := RP_meas s t
  have hRi : Integrable (RP s t) (rowM N) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (RP_mem s t v).1]; exact (RP_mem s t v).2)
  have hRi2 : Integrable (fun v => RP s t v ^ 2) (rowM N) :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1
      (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [(RP_mem s t v).1, (RP_mem s t v).2])
  have hEi : Integrable (fun v => Real.exp (-(l * RP s t v))) (rowM N) :=
    Integrable.of_bound ((hm.const_mul l).neg.exp).aestronglyMeasurable 1
      (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_one_iff.2
        have := (RP_mem s t v).1; nlinarith)
  have hpt : ∀ v, Real.exp (-(l * RP s t v)) ≤ 1 - l * RP s t v + l ^ 2 / 2 * RP s t v ^ 2 := by
    intro v
    have := exp_neg_le_quad (mul_nonneg hl (RP_mem s t v).1)
    have e : (l * RP s t v) ^ 2 / 2 = l ^ 2 / 2 * RP s t v ^ 2 := by ring
    linarith
  have hA1 : Integrable (fun v => 1 - l * RP s t v) (rowM N) := (integrable_const 1).sub (hRi.const_mul l)
  have hA2 : Integrable (fun v => l ^ 2 / 2 * RP s t v ^ 2) (rowM N) := hRi2.const_mul _
  have hA3 : Integrable (fun v => 1 - l * RP s t v + l ^ 2 / 2 * RP s t v ^ 2) (rowM N) := hA1.add hA2
  have hint := integral_mono hEi hA3 hpt
  have e1 := integral_add hA1 hA2
  have e2 := integral_sub (integrable_const (1 : ℝ)) (hRi.const_mul l) (μ := rowM N)
  rw [e1, e2, integral_const_mul, integral_const_mul, RP_int, RP_int_sq, integral_const] at hint
  simp only [probReal_univ, smul_eq_mul, one_mul] at hint
  refine hint.trans ?_
  have := Real.add_one_le_exp (-(l * (1 / 2) ^ N) + l ^ 2 * (1 / 3) ^ N / 2)
  linarith

/-- **Lower tail of the generic mass of one pattern.** -/
lemma low_one (A : Finset (State N)) (hA : A.card ≤ 3) (hN : 4 ≤ N) (s t : State N) :
    rowsOutM A {g | ∑ r : {r // r ∉ A}, RP s t (g r) < 1 / 2} ≤
      ENNReal.ofReal (Real.exp (-((3 / 2 : ℝ) ^ N / 32))) := by
  set l : ℝ := (3 / 2 : ℝ) ^ N / 4 with hl
  have hl0 : 0 ≤ l := by positivity
  set F : ({r // r ∉ A} → Fin N → ℝ) → ℝ := fun g => ∏ r : {r // r ∉ A}, Real.exp (-(l * RP s t (g r)))
    with hF
  have hFeq : ∀ g, F g = Real.exp (-(l * ∑ r : {r // r ∉ A}, RP s t (g r))) := fun g => by
    simp only [hF]
    rw [← Real.exp_sum, mul_sum, ← sum_neg_distrib]
  have hFm : Measurable F :=
    Finset.measurable_prod _ fun r _ => ((RP_meas s t).comp (measurable_pi_apply r)).const_mul l |>.neg.exp
  have hF0 : ∀ g, 0 ≤ F g := fun g => prod_nonneg fun r _ => (Real.exp_pos _).le
  have hF1 : ∀ g, F g ≤ 1 := fun g => prod_le_one (fun r _ => (Real.exp_pos _).le) fun r _ =>
    Real.exp_le_one_iff.2 (by have := (RP_mem s t (g r)).1; nlinarith)
  have hFi : Integrable F (rowsOutM A) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1
      (ae_of_all _ fun g => by rw [Real.norm_eq_abs, abs_of_nonneg (hF0 g)]; exact hF1 g)
  -- Markov
  have hsub : {g | ∑ r : {r // r ∉ A}, RP s t (g r) < 1 / 2} ⊆ {g | Real.exp (-(l / 2)) ≤ F g} := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [hFeq]
    apply Real.exp_le_exp.2
    nlinarith
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hF0) hFi (Real.exp (-(l / 2)))
  -- the integral factorises
  have hint : ∫ g, F g ∂rowsOutM A = ∏ _r : {r // r ∉ A}, ∫ v, Real.exp (-(l * RP s t v)) ∂rowM N := by
    rw [hF]; unfold rowsOutM
    exact integral_fintype_prod_eq_prod (fun _ v => Real.exp (-(l * RP s t v)))
  set c := -(l * (1 / 2) ^ N) + l ^ 2 * (1 / 3) ^ N / 2 with hc
  have hprod : ∫ g, F g ∂rowsOutM A ≤ Real.exp (Fintype.card {r // r ∉ A} * c) := by
    rw [hint]
    calc ∏ _r : {r // r ∉ A}, ∫ v, Real.exp (-(l * RP s t v)) ∂rowM N
        ≤ ∏ _r : {r // r ∉ A}, Real.exp c :=
          prod_le_prod (fun _ _ => integral_nonneg fun v => (Real.exp_pos _).le)
            fun _ _ => RP_mgf_neg s t hl0
      _ = Real.exp (Fintype.card {r // r ∉ A} * c) := by
          rw [prod_const, ← Real.exp_nat_mul]; rfl
  -- the exponent
  have hK := card_generic A
  have hA' : (A.card : ℝ) ≤ 3 := by exact_mod_cast hA
  have h2N : (16 : ℝ) ≤ 2 ^ N := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN; norm_num at this ⊢; linarith
  have hexp : l / 2 + Fintype.card {r // r ∉ A} * c ≤ -((3 / 2 : ℝ) ^ N / 32) := by
    rw [hc, hK]
    have e1 : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num
    have e2 : (2 : ℝ) ^ N * (1 / 3) ^ N = (2 / 3) ^ N := by rw [← mul_pow]; norm_num
    have e3 : (3 / 2 : ℝ) ^ N * (2 / 3) ^ N = 1 := by rw [← mul_pow]; norm_num
    have hp : (0 : ℝ) < (1 / 2) ^ N := by positivity
    have hq : (0 : ℝ) < (1 / 3) ^ N := by positivity
    have h3 : (A.card : ℝ) * (1 / 2) ^ N ≤ 3 / 16 := by
      have : (1 / 2 : ℝ) ^ N ≤ 1 / 16 := by
        rw [one_div_pow, one_div_le_one_div (by positivity) (by norm_num)]; exact h2N
      nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
    have h4 : ((2 : ℝ) ^ N - A.card) * (1 / 3) ^ N ≤ (2 / 3) ^ N := by
      rw [← e2]; nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
    have hl2 : l ^ 2 * (2 / 3) ^ N = l / 4 := by
      rw [hl]
      calc ((3 / 2 : ℝ) ^ N / 4) ^ 2 * (2 / 3) ^ N = (3 / 2 : ℝ) ^ N * ((3 / 2) ^ N * (2 / 3) ^ N) / 16 := by
            ring
        _ = (3 / 2 : ℝ) ^ N / 4 / 4 := by rw [e3]; ring
    have : ((2 : ℝ) ^ N - A.card) * (-(l * (1 / 2) ^ N) + l ^ 2 * (1 / 3) ^ N / 2) =
        -l * ((2 : ℝ) ^ N * (1 / 2) ^ N) + l * (A.card * (1 / 2) ^ N) +
          l ^ 2 / 2 * (((2 : ℝ) ^ N - A.card) * (1 / 3) ^ N) := by ring
    rw [this, e1]
    have h5 : l ^ 2 / 2 * (((2 : ℝ) ^ N - A.card) * (1 / 3) ^ N) ≤ l ^ 2 / 2 * (2 / 3) ^ N :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : l * (A.card * (1 / 2) ^ N) ≤ l * (3 / 16) := mul_le_mul_of_nonneg_left h3 hl0
    have h7 : l ^ 2 / 2 * (2 / 3) ^ N = l / 8 := by rw [div_mul_eq_mul_div, hl2]; ring
    have h8 : (3 / 2 : ℝ) ^ N / 32 = l / 8 := by rw [hl]; ring
    rw [h8]
    linarith
  -- assemble
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  have hpos := Real.exp_pos (-(l / 2))
  have hmk' : (rowsOutM A).real {g | Real.exp (-(l / 2)) ≤ F g} ≤
      Real.exp (l / 2) * ∫ g, F g ∂rowsOutM A := by
    have e : Real.exp (l / 2) * Real.exp (-(l / 2)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [measureReal_nonneg (μ := rowsOutM A) (s := {g | Real.exp (-(l / 2)) ≤ F g}),
      Real.exp_pos (l / 2)]
  refine hmk'.trans ?_
  calc Real.exp (l / 2) * ∫ g, F g ∂rowsOutM A ≤ Real.exp (l / 2) * Real.exp (Fintype.card {r // r ∉ A} * c) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (l / 2 + Fintype.card {r // r ∉ A} * c) := by rw [Real.exp_add]
    _ ≤ Real.exp (-((3 / 2 : ℝ) ^ N / 32)) := Real.exp_le_exp.2 hexp


/-! ### Upper tail (Chebyshev) -/

/-- **Upper tail of the generic mass of one pattern.** -/
lemma up_one (A : Finset (State N)) (s t : State N) :
    rowsOutM A {g | 3 / 2 < ∑ r : {r // r ∉ A}, RP s t (g r)} ≤ ENNReal.ofReal (4 * (2 / 3 : ℝ) ^ N) := by
  set Y : {r // r ∉ A} → ({r // r ∉ A} → Fin N → ℝ) → ℝ := fun r g => RP s t (g r) with hY
  have hYm : ∀ r, Measurable (Y r) := fun r => (RP_meas s t).comp (measurable_pi_apply r)
  have hY01 : ∀ r g, Y r g ∈ Set.Icc (0 : ℝ) 1 := fun r g => RP_mem s t (g r)
  have hYL : ∀ r, MemLp (Y r) 2 (rowsOutM A) := fun r =>
    MemLp.of_bound (hYm r).aestronglyMeasurable 1
      (ae_of_all _ fun g => by rw [Real.norm_eq_abs, abs_of_nonneg (hY01 r g).1]; exact (hY01 r g).2)
  have hind : iIndepFun Y (rowsOutM A) := by
    unfold rowsOutM
    exact iIndepFun_pi (X := fun (_ : {r // r ∉ A}) (v : Fin N → ℝ) => RP s t v)
      fun _ => (RP_meas s t).aemeasurable
  set X := ∑ r ∈ (univ : Finset {r // r ∉ A}), Y r with hX
  have hXapp : ∀ g, X g = ∑ r : {r // r ∉ A}, RP s t (g r) := fun g => by
    rw [hX, Finset.sum_apply]
  have hXL : MemLp X 2 (rowsOutM A) := memLp_finset_sum' _ fun r _ => hYL r
  have hvar : variance X (rowsOutM A) = ∑ r ∈ (univ : Finset {r // r ∉ A}), variance (Y r) (rowsOutM A) :=
    IndepFun.variance_sum (fun r _ => hYL r) fun i _ j _ hij => hind.indepFun hij
  have hint1 : ∀ r, ∫ g, Y r g ∂rowsOutM A = (1 / 2) ^ N := fun r => by
    simp only [hY]; unfold rowsOutM
    rw [integral_pi_eval (rowM N) (g := RP s t) (RP_meas s t).aestronglyMeasurable r, RP_int]
  have hint2 : ∀ r, ∫ g, (Y r ^ 2) g ∂rowsOutM A = (1 / 3) ^ N := fun r => by
    simp only [hY, Pi.pow_apply]; unfold rowsOutM
    rw [integral_pi_eval (rowM N) (g := fun v => RP s t v ^ 2)
      ((RP_meas s t).pow_const 2).aestronglyMeasurable r, RP_int_sq]
  have hK := card_generic A
  have hKle : (Fintype.card {r // r ∉ A} : ℝ) ≤ 2 ^ N := by rw [hK]; linarith [Nat.cast_nonneg (α := ℝ) A.card]
  have hvarle : variance X (rowsOutM A) ≤ (2 / 3) ^ N := by
    rw [hvar]
    calc ∑ r ∈ (univ : Finset {r // r ∉ A}), variance (Y r) (rowsOutM A)
        ≤ ∑ _r ∈ (univ : Finset {r // r ∉ A}), (1 / 3 : ℝ) ^ N :=
          sum_le_sum fun r _ => (variance_le_expectation_sq (hYm r).aestronglyMeasurable).trans
            (le_of_eq (hint2 r))
      _ = Fintype.card {r // r ∉ A} * (1 / 3 : ℝ) ^ N := by rw [sum_const, nsmul_eq_mul, card_univ]
      _ ≤ 2 ^ N * (1 / 3) ^ N := mul_le_mul_of_nonneg_right hKle (by positivity)
      _ = (2 / 3) ^ N := by rw [← mul_pow]; norm_num
  have hmean : ∫ g, X g ∂rowsOutM A ≤ 1 := by
    have : ∫ g, X g ∂rowsOutM A = Fintype.card {r // r ∉ A} * (1 / 2 : ℝ) ^ N := by
      rw [hX]
      simp only [Finset.sum_apply]
      rw [integral_finset_sum _ fun r _ => (hYL r).integrable one_le_two]
      simp only [hint1, sum_const, nsmul_eq_mul, card_univ]
    rw [this]
    calc (Fintype.card {r // r ∉ A} : ℝ) * (1 / 2) ^ N ≤ 2 ^ N * (1 / 2) ^ N :=
          mul_le_mul_of_nonneg_right hKle (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hsub : {g | 3 / 2 < ∑ r : {r // r ∉ A}, RP s t (g r)} ⊆
      {g | 1 / 2 ≤ |X g - ∫ g, X g ∂rowsOutM A|} := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [hXapp, le_abs]; left; linarith
  refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq hXL (by norm_num)).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-! ### The two fields -/

/-- `low` for any fixed-row set of size `≤ 3`. -/
theorem low_cond_gen (A : Finset (State N)) (hA : A.card ≤ 3) (hN : 4 ≤ N) (s : State N)
    (f : A → Fin N → ℝ) :
    rowsOutM A {g | ¬ ∀ t : State N, 1 / 2 ≤
      ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s (glueRows A f g))) r t} ≤
      ENNReal.ofReal (2 ^ N * Real.exp (-((3 / 2 : ℝ) ^ N / 32))) := by
  have hsub : {g | ¬ ∀ t : State N, 1 / 2 ≤ ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s (glueRows A f g))) r t} ⊆
      ⋃ t : State N, {g | ∑ r : {r // r ∉ A}, RP s t (g r) < 1 / 2} := by
    intro g hg
    have hg' : ∃ t : State N, ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s (glueRows A f g))) r t < 1 / 2 := by
      by_contra h
      exact hg fun t => not_lt.1 fun h' => h ⟨t, h'⟩
    obtain ⟨t, ht⟩ := hg'
    rw [sum_compl_glue] at ht
    exact Set.mem_iUnion.2 ⟨t, ht⟩
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  calc ∑ t : State N, rowsOutM A {g | ∑ r : {r // r ∉ A}, RP s t (g r) < 1 / 2}
      ≤ ∑ _t : State N, ENNReal.ofReal (Real.exp (-((3 / 2 : ℝ) ^ N / 32))) :=
        sum_le_sum fun t _ => low_one A hA hN s t
    _ = ENNReal.ofReal (2 ^ N * Real.exp (-((3 / 2 : ℝ) ^ N / 32))) := by
        rw [sum_const, card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        simp [ENNReal.ofReal_pow]

/-- `upTe` for any fixed-row set containing `s`. -/
theorem upTe_cond_gen (A : Finset (State N)) {s : State N} (hsA : s ∈ A) (f : A → Fin N → ℝ) :
    rowsOutM A {g | ¬ ∑ r ∈ Aᶜ,
      fullProb (tpmOf (flipP s (glueRows A f g))) r (teW (glueRows A f g) s) ≤ 3 / 2} ≤
      ENNReal.ofReal (4 * (2 / 3 : ℝ) ^ N) := by
  set t0 : State N := fun k => if (1 / 2 : ℝ) < clamp01 (f ⟨s, hsA⟩ k) then s k else !s k with ht0
  have hte : ∀ g, teW (glueRows A f g) s = t0 := fun g => by
    funext k; simp only [teW, ht0, glueRows_of_mem A f g hsA]
  have hsub : {g | ¬ ∑ r ∈ Aᶜ,
      fullProb (tpmOf (flipP s (glueRows A f g))) r (teW (glueRows A f g) s) ≤ 3 / 2} ⊆
      {g | 3 / 2 < ∑ r : {r // r ∉ A}, RP s t0 (g r)} := by
    intro g hg
    have hg' := not_le.1 hg
    rw [hte, sum_compl_glue] at hg'
    exact hg'
  exact (measure_mono hsub).trans (up_one A s t0)

end Census
end IIT
