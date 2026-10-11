/-
Census, B1 small cuts (W12 §6): **the Chernoff bound for one centre row, one cut, one cell**.

`scE r0 K m mp T B` : floor `y_{r0,j} ≥ m` for all `j`, tilt `X(r0) ≤ B`, and `Σ_{j ∉ K} V_j ≤ T` with
`V_j = min(log₂(y_j / X_j), log₂(y_j / m'))`, `X_j` the subcube mean of column `j`. With `t = n ln 2` and `μ`:

  `P(scE) ≤ e^{n ln 2 · T + μ B} · R^{N - |K|}`

where `R` bounds the per-column integral (`sc_col_bound` + `sc_cell_bound`); the columns of `K` contribute `≤ 1`.
-/
import IIT.Census.B1SmallCutCert

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The per-column small-cut term. -/
noncomputable def scV (r0 : State N) (K : Finset (Fin N)) (mp : ℝ) (c : State N → ℝ) : ℝ :=
  min (Real.logb 2 (clamp01 (c r0) / scX r0 K c)) (Real.logb 2 (clamp01 (c r0) / mp))

lemma measurable_scX (r0 : State N) (K : Finset (Fin N)) : Measurable (scX r0 K) := by
  unfold scX
  exact (Finset.measurable_sum _ fun r _ => continuous_clamp01.measurable.comp (measurable_pi_apply r)).div_const _

lemma measurable_scV (r0 : State N) (K : Finset (Fin N)) (mp : ℝ) : Measurable (scV r0 K mp) := by
  have hy : Measurable fun c : State N → ℝ => clamp01 (c r0) :=
    continuous_clamp01.measurable.comp (measurable_pi_apply r0)
  unfold scV Real.logb
  exact (((hy.div (measurable_scX r0 K)).log).div_const _).min (((hy.div_const mp).log).div_const _)

/-- The event of one centre row, one cut, one cell. -/
def scE (r0 : State N) (K : Finset (Fin N)) (m mp T B : ℝ) : Set (Param N) :=
  {w | (∀ j, m ≤ clamp01 (w r0 j)) ∧ XW w r0 ≤ B ∧ ∑ j ∈ Kᶜ, scV r0 K mp (fun r => w r j) ≤ T}

/-- **Chernoff for one centre row, one cut.** -/
theorem sc_chernoff (r0 : State N) (K : Finset (Fin N)) {a b : Fin N} (hab : ({a, b} : Finset (Fin N)) ⊆ K)
    (hne : a ≠ b) {m mp : ℝ} (hm : 0 < m) (hmp : 0 < mp) (n μ : ℕ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal (scG mp n μ (clamp01 u))) u ∂unif ≤
      ENNReal.ofReal R) (T B : ℝ) :
    cubeM N (scE r0 K m mp T B) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B) * R ^ (N - K.card)) := by
  classical
  haveI := colLaw_isProb (N := N)
  set F : Fin 2 → Fin N → (State N → ℝ) → ℝ := ![fun j c => if j ∈ K then 0 else scV r0 K mp c,
    fun _ c => -Real.log (clamp01 (c r0))] with hF
  have hFm : ∀ k j, Measurable (F k j) := by
    intro k j
    fin_cases k
    · simp only [hF, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      split_ifs
      · exact measurable_const
      · exact measurable_scV r0 K mp
    · simp only [hF, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      exact (continuous_clamp01.measurable.comp (measurable_pi_apply r0)).log.neg
  set A : Fin 2 → ℝ := ![T, B] with hA
  set tt : Fin 2 → ℝ := ![(n : ℝ) * Real.log 2, μ] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 2)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
    · simp [htt]
  set W : Fin N → Set (State N → ℝ) := fun _ => {c | m ≤ clamp01 (c r0)} with hW
  have hWm : ∀ j, MeasurableSet (W j) := fun j =>
    measurableSet_le measurable_const (continuous_clamp01.measurable.comp (measurable_pi_apply r0))
  have hmain := cubeM_chernoff_cols univ F hFm A tt htt0 W hWm
  have hsub : scE r0 K m mp T B ⊆ {w | (∀ j, (fun r => w r j) ∈ W j) ∧
      ∀ k ∈ (univ : Finset (Fin 2)), ∑ j, F k j (fun r => w r j) ≤ A k} := by
    rintro w ⟨hfl, hX, hS⟩
    refine ⟨fun j => hfl j, fun k _ => ?_⟩
    fin_cases k
    · simp only [hF, hA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [sum_ite, sum_const_zero, zero_add, filter_not, ← compl_eq_univ_sdiff]
      simpa using hS
    · simp only [hF, hA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      exact hX
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsumA : ∑ k ∈ (univ : Finset (Fin 2)), tt k * A k = (n : ℝ) * Real.log 2 * T + μ * B := by
    simp [htt, hA, Fin.sum_univ_two]
  rw [hsumA]
  -- the columns
  have hcolK : ∀ j ∈ K, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ 1 := by
    intro j hj
    refine (setLIntegral_mono' (g := fun _ => (1 : ENNReal)) (hWm j) fun c _ => ?_).trans ?_
    · simp only [Fin.sum_univ_two, hF, htt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        if_pos hj, mul_zero, zero_add]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 ?_)
      have := Real.log_nonpos (clamp01_nonneg (c r0)) (clamp01_le_one _)
      have : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
      nlinarith
    · rw [setLIntegral_const]
      calc 1 * (colLaw N) (W j) ≤ 1 * 1 := mul_le_mul' le_rfl prob_le_one
        _ = 1 := one_mul 1
  have hcolN : ∀ j ∉ K, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ ENNReal.ofReal R := by
    intro j hj
    have e : ∀ c, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c)) =
        ENNReal.ofReal (Real.exp (-((n : ℝ) * Real.log 2 * min (Real.logb 2 (clamp01 (c r0) / scX r0 K c))
          (Real.logb 2 (clamp01 (c r0) / mp)) + μ * -Real.log (clamp01 (c r0))))) := by
      intro c
      simp only [Fin.sum_univ_two, hF, htt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        if_neg hj, scV]
    simp_rw [e]
    rw [← lintegral_indicator (hWm j)]
    exact (sc_col_bound r0 K hab hne hm hmp).trans hR
  -- the product
  rw [← Finset.prod_compl_mul_prod K]
  have hp1 : ∏ j ∈ K, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ 1 := prod_le_one' fun j hj => hcolK j hj
  have hp2 : ∏ j ∈ Kᶜ, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ ENNReal.ofReal R ^ (N - K.card) := by
    calc _ ≤ ∏ _j ∈ Kᶜ, ENNReal.ofReal R := prod_le_prod' fun j hj => hcolN j (mem_compl.1 hj)
      _ = ENNReal.ofReal R ^ (N - K.card) := by rw [prod_const, card_compl, Fintype.card_fin]
  calc ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B)) *
        ((∏ j ∈ Kᶜ, _) * ∏ j ∈ K, _)
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B)) * (ENNReal.ofReal R ^ (N - K.card) * 1) :=
        mul_le_mul' le_rfl (mul_le_mul' hp2 hp1)
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B) * R ^ (N - K.card)) := by
        rw [mul_one, ← ENNReal.ofReal_pow hR0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

end Census
end IIT
