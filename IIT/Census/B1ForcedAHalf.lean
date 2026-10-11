/-
Census, B1 forced leaves, part A1: half-mean regularity (leaves `bHalfC`, `bHalfE`), unconditional.

For a state `t` and a unit `j`, the column mean of `clamp01 (w r j)` over the `2^{N-1}` rows `r` with
`r j = t j` is a mean of independent uniforms: Hoeffding gives deviation `> δ` with probability
`≤ 2 e^{-2^N δ²}`; with `δ = 1/(N+1)` and a union over all `(t, j)` this is superexponentially small.
-/
import IIT.Census.B1Lemma43
import IIT.Census.B1Chernoff

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-- The column half-mean over the rows agreeing with `t` at `j`. -/
def faColMean (w : Param N) (t : State N) (j : Fin N) : ℝ :=
  (∑ r ∈ agree {j} t, clamp01 (w r j)) / (2 : ℝ) ^ (N - 1)

lemma cmean_single_eq (w : Param N) (t : State N) (j : Fin N) :
    cmean w {j} t j = faColMean w t j := by
  unfold cmean faColMean; rw [card_singleton]

lemma fa_integral_clamp : ∫ v, clamp01 v ∂unif = 1 / 2 := by
  have h1 := integral_cl_pow 1
  simp only [pow_one, Nat.cast_one] at h1
  rw [h1]; norm_num

lemma fa_clamp01_one_sub (x : ℝ) : clamp01 (1 - x) = 1 - clamp01 x := clamp01_one_sub x

/-- **Hoeffding for one half-mean.** -/
theorem fa_col_dev (hN : 1 ≤ N) (t : State N) (j : Fin N) {δ : ℝ} (hδ : 0 ≤ δ) :
    cubeM N {w | δ < |faColMean w t j - 1 / 2|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 ^ N * δ ^ 2))) := by
  set A := agree {j} t with hA
  have hcard : A.card = 2 ^ (N - 1) := by rw [hA, card_agree, card_singleton]
  have hc : ((A.card : ℕ) : ℝ) = (2 : ℝ) ^ (N - 1) := by rw [hcard]; push_cast; ring
  have h2 : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have hφj : Measurable fun v : Fin N → ℝ => clamp01 (v j) :=
    clamp01_measurable.comp (measurable_pi_apply j)
  have hind : iIndepFun (fun (r : State N) (w : Param N) => clamp01 (w r j)) (cubeM N) := by
    unfold cubeM
    exact iIndepFun_pi (X := fun (_ : State N) (v : Fin N → ℝ) => clamp01 (v j))
      fun _ => hφj.aemeasurable
  have hmeas : ∀ r, AEMeasurable (fun w : Param N => clamp01 (w r j)) (cubeM N) :=
    fun r => (hφj.comp (measurable_pi_apply r)).aemeasurable
  have hb : ∀ r ∈ A, ∀ᵐ w ∂(cubeM N), clamp01 (w r j) ∈ Set.Icc 0 ((fun _ => (1 : ℝ)) r) :=
    fun r _ => ae_of_all _ fun w => ⟨clamp01_nonneg _, clamp01_le_one _⟩
  have hε : (0 : ℝ) ≤ 2 ^ (N - 1) * δ := by positivity
  have h := hoeffding_abs (μ := cubeM N) (X := fun r w => clamp01 (w r j)) A hind hmeas hb hε
  have hint : ∀ r, ∫ w, clamp01 (w r j) ∂(cubeM N) = 1 / 2 := by
    intro r
    unfold cubeM
    rw [integral_pi_eval (rowM N) (g := fun v : Fin N → ℝ => clamp01 (v j)) hφj.aestronglyMeasurable r]
    unfold rowM
    rw [integral_pi_eval unif clamp01_measurable.aestronglyMeasurable j, fa_integral_clamp]
  simp only [hint, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
  have hsub : {w : Param N | δ < |faColMean w t j - 1 / 2|} ⊆
      {w | 2 ^ (N - 1) * δ ≤ |∑ r ∈ A, (clamp01 (w r j) - 1 / 2)|} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    have e : faColMean w t j - 1 / 2 = (∑ r ∈ A, (clamp01 (w r j) - 1 / 2)) / 2 ^ (N - 1) := by
      unfold faColMean
      rw [← hA, sum_sub_distrib, sum_const, nsmul_eq_mul, hc]
      field_simp
    rw [e, abs_div, abs_of_pos h2, lt_div_iff₀ h2] at hw
    linarith
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hc]
  have e2 : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : -2 * (2 ^ (N - 1) * δ) ^ 2 / (2 : ℝ) ^ (N - 1) = -(2 ^ N * δ ^ 2) := by
    rw [e2]; field_simp
  rw [this]

lemma fa_cube_bound : ∀ᶠ N : ℕ in atTop, 3 * (N : ℝ) * ((N : ℝ) + 1) ^ 2 ≤ 2 ^ N := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 3
    (r := (1 / 2 : ℝ)) (by rw [abs_of_pos (by norm_num)]; norm_num)
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12)),
    eventually_ge_atTop 1] with N hN h1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  have e : (N : ℝ) ^ 3 * (1 / 2) ^ N = (N : ℝ) ^ 3 / 2 ^ N := by rw [div_pow, one_pow]; ring
  rw [e, div_lt_iff₀ hp] at hN
  have h2 : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
  have h3 : 3 * (N : ℝ) * ((N : ℝ) + 1) ^ 2 ≤ 12 * (N : ℝ) ^ 3 := by nlinarith
  linarith

lemma fa_half_arith (hN1 : (1 : ℝ) ≤ N) (hb : 3 * (N : ℝ) * ((N : ℝ) + 1) ^ 2 ≤ 2 ^ N) :
    (2 : ℝ) ^ N * N * (2 * Real.exp (-(2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2))) ≤
      Real.exp (-((10105 / 10000 : ℝ) * N)) := by
  have hp1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hk : 3 * (N : ℝ) ≤ 2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2 := by
    rw [div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity)]; linarith
  have hE : Real.exp (-(2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2)) ≤ Real.exp (-(3 * N)) :=
    Real.exp_le_exp.2 (by linarith)
  have h2e : (2 : ℝ) ^ N ≤ Real.exp N := by
    have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc (2 : ℝ) ^ N ≤ Real.exp 1 ^ N := pow_le_pow_left₀ (by norm_num) this N
      _ = Real.exp N := by rw [← Real.exp_nat_mul]; ring_nf
  have hq : 2 * (N : ℝ) ≤ Real.exp (98 / 100 * N) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 98 / 100 * (N : ℝ)) (by positivity)
    nlinarith [sq_nonneg ((N : ℝ) - 1062 / 1000)]
  have hN0 : (0 : ℝ) ≤ N := by linarith
  calc (2 : ℝ) ^ N * N * (2 * Real.exp (-(2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2)))
      = (2 : ℝ) ^ N * (2 * N) * Real.exp (-(2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2)) := by ring
    _ ≤ Real.exp N * Real.exp (98 / 100 * N) * Real.exp (-(3 * N)) := by
        gcongr
    _ = Real.exp (-((10105 / 10000 : ℝ) * N) + -(95 / 10000 * (N : ℝ))) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-((10105 / 10000 : ℝ) * N)) := Real.exp_le_exp.2 (by linarith)

/-- **All half-means are regular**, superexponentially. -/
theorem fa_half_all : ∀ᶠ N : ℕ in atTop,
    cubeM N {w | ∃ t j, (1 / ((N : ℝ) + 1)) < |faColMean w t j - 1 / 2|} ≤
      ENNReal.ofReal (Real.exp (-((10105 / 10000 : ℝ) * N))) := by
  filter_upwards [fa_cube_bound, eventually_ge_atTop 1] with N hb h1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hset : {w : Param N | ∃ t j, (1 / ((N : ℝ) + 1)) < |faColMean w t j - 1 / 2|} =
      ⋃ p : State N × Fin N, {w | (1 / ((N : ℝ) + 1)) < |faColMean w p.1 p.2 - 1 / 2|} := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [hset]
  have hc : ((Fintype.card (State N × Fin N) : ℕ) : ℝ) = (2 : ℝ) ^ N * N := by
    rw [Fintype.card_prod, Fintype.card_fin, show Fintype.card (State N) = 2 ^ N by simp]
    push_cast; ring
  have hδ : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hU := cubeM_iUnion_le (fun p : State N × Fin N =>
    {w : Param N | (1 / ((N : ℝ) + 1)) < |faColMean w p.1 p.2 - 1 / 2|})
    (fun p => fa_col_dev h1 p.1 p.2 hδ)
  refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hc]
  exact fa_half_arith hN1 hb

end

end Census
end IIT
