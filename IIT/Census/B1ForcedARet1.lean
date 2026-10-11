/-
Census, B1 forced leaves, part A2: the core Chernoff bound for the field `retR1` (W7 X3, `D_total ≥ N/400`).

Rows `r0` (entries `y`), `r1 = r0^x` (entries `U`) and `s` (entries `x_k = max(y_s, 1 - y_s)`):
the event  T: `XW(r0) ≤ B`,  L: `∑ -ln x_k ≤ XW(r0) + L`,  D: `∑_{j≠x} ln(y_j/U_j) < N/400`
has probability `≤ e^{11 B + 3 L + N/100} (3/160)^{N-1}` (multipliers 11, 3, 4: per column
`E y^4 E U^4 E x^3 = (1/5)(1/5)(15/32)`). When `s ∈ {r0, r1}` the link is dropped:
`≤ e^{11 B + N/100} (1/40)^{N-1}` (multipliers 11, 4: `E y^7 E U^4 = 1/40`).
-/
import IIT.Census.B1Defs
import IIT.Census.B1NearUniv

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

lemma fa_ae_unif_pos : ∀ᵐ y ∂unif, 0 < clamp01 y ∧ clamp01 y = y := by
  rw [unif_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  have : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy.1.le]
  exact ⟨by rw [this]; exact hy.1, this⟩

lemma fa_lint_pow_log (n : ℕ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log (clamp01 y))) ∂unif =
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  rw [← lintegral_unif_pow n]
  refine lintegral_congr_ae ?_
  filter_upwards [fa_ae_unif_pos] with y hy
  rw [Real.exp_nat_mul, Real.exp_log hy.1]

lemma fa_fold_pos (u : ℝ) : 0 < max (clamp01 u) (1 - clamp01 u) := by
  rcases le_total (clamp01 u) (1 / 2) with h | h
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)

lemma fa_lint_fold_log (n : ℕ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log (max (clamp01 u) (1 - clamp01 u)))) ∂unif =
      ENNReal.ofReal (2 * (1 - (1 / 2 : ℝ) ^ (n + 1)) / ((n : ℝ) + 1)) := by
  rw [← lintegral_unif_fold_pow n]
  refine lintegral_congr fun u => ?_
  rw [Real.exp_nat_mul, Real.exp_log (fa_fold_pos u)]

/-- Factorisation of a column integral. -/
lemma fa_triple_fact (A B C : ℝ → ℝ) (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) :
    ∫⁻ y in Set.univ, ∫⁻ u, ∫⁻ x, ENNReal.ofReal (Real.exp (A y + B u + C x)) ∂unif ∂unif ∂unif =
      (∫⁻ y, ENNReal.ofReal (Real.exp (A y)) ∂unif) * (∫⁻ u, ENNReal.ofReal (Real.exp (B u)) ∂unif) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (C x)) ∂unif := by
  rw [Measure.restrict_univ]
  have mA : Measurable fun y => ENNReal.ofReal (Real.exp (A y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hA)
  have mB : Measurable fun y => ENNReal.ofReal (Real.exp (B y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hB)
  have mC : Measurable fun y => ENNReal.ofReal (Real.exp (C y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hC)
  have e : ∀ y u x, ENNReal.ofReal (Real.exp (A y + B u + C x)) =
      ENNReal.ofReal (Real.exp (A y)) * ENNReal.ofReal (Real.exp (B u)) *
        ENNReal.ofReal (Real.exp (C x)) := by
    intro y u x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_add, ← Real.exp_add]
  simp_rw [e]
  simp_rw [lintegral_const_mul _ mC]
  simp_rw [lintegral_mul_const _ (mB.const_mul _), lintegral_const_mul _ mB]
  rw [lintegral_mul_const _ (mA.mul_const _), lintegral_mul_const _ mA]

/-- product over columns with one exceptional column -/
lemma fa_prod_except (x : Fin N) (F : Fin N → ENNReal) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hF : ∀ i, i ≠ x → F i = ENNReal.ofReal a) (hFx : F x ≤ ENNReal.ofReal b) :
    ∏ i, F i ≤ ENNReal.ofReal (a ^ (N - 1)) := by
  rw [← mul_prod_erase univ F (mem_univ x)]
  have h1 : ∏ i ∈ univ.erase x, F i = ENNReal.ofReal (a ^ (N - 1)) := by
    rw [prod_congr rfl fun i hi => hF i (ne_of_mem_erase hi), prod_const, card_erase_of_mem (mem_univ x),
      card_univ, Fintype.card_fin, ENNReal.ofReal_pow ha]
  rw [h1]
  calc F x * ENNReal.ofReal (a ^ (N - 1)) ≤ ENNReal.ofReal 1 * ENNReal.ofReal (a ^ (N - 1)) := by
        gcongr; exact hFx.trans (ENNReal.ofReal_le_ofReal hb)
    _ = _ := by simp

/-- the three constraint functions -/
def faR1f (x : Fin N) : Fin 3 → Fin N → ℝ × ℝ × ℝ → ℝ :=
  ![fun _ p => -Real.log (clamp01 p.1),
    fun _ p => -Real.log (max (clamp01 p.2.2) (1 - clamp01 p.2.2)) + Real.log (clamp01 p.1),
    fun i p => if i = x then 0 else Real.log (clamp01 p.1) - Real.log (clamp01 p.2.1)]

lemma faR1f_meas (x : Fin N) (k : Fin 3) (i : Fin N) : Measurable (faR1f x k i) := by
  have hl : Measurable fun v : ℝ => Real.log (clamp01 v) := Real.measurable_log.comp clamp01_measurable
  have hf : Measurable fun v : ℝ => Real.log (max (clamp01 v) (1 - clamp01 v)) :=
    Real.measurable_log.comp (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  fin_cases k
  · exact (hl.comp measurable_fst).neg
  · exact (hf.comp (measurable_snd.comp measurable_snd)).neg.add (hl.comp measurable_fst)
  · show Measurable fun p : ℝ × ℝ × ℝ =>
      if i = x then (0 : ℝ) else Real.log (clamp01 p.1) - Real.log (clamp01 p.2.1)
    split_ifs
    · exact measurable_const
    · exact (hl.comp measurable_fst).sub (hl.comp (measurable_fst.comp measurable_snd))

lemma fa_log_div_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log (a / b) = Real.log a - Real.log b :=
  Real.log_div ha.ne' hb.ne'

lemma fa_clamp_pos {w : Param N} (hw : w ∈ openCube N) (r : State N) (i : Fin N) :
    0 < clamp01 (w r i) ∧ clamp01 (w r i) = w r i := by
  have h := hw r i
  have : clamp01 (w r i) = w r i := by unfold clamp01; rw [min_eq_right h.2.le, max_eq_right h.1.le]
  exact ⟨by rw [this]; exact h.1, this⟩

/-- the D-sum, rewritten -/
lemma fa_Dsum_eq {w : Param N} (hw : w ∈ openCube N) (r0 : State N) (x : Fin N) :
    ∑ i, faR1f x 2 i (w r0 i, w (flipAt x r0) i, 0) =
      ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) := by
  simp only [faR1f, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [← add_sum_erase univ _ (mem_univ x), if_pos rfl, zero_add]
  refine sum_congr rfl fun j hj => ?_
  rw [if_neg (ne_of_mem_erase hj), fa_log_div_eq (fa_clamp_pos hw _ _).1 (fa_clamp_pos hw _ _).1]

/-- **Core bound, generic case** (`s ∉ {r0, r0^x}`). -/
theorem fa_r1_core (s r0 : State N) (x : Fin N) (hs0 : r0 ≠ s) (hs1 : flipAt x r0 ≠ s) (B L : ℝ) :
    cubeM N {w | w ∈ openCube N ∧ XW w r0 ≤ B ∧ ∑ k, -Real.log (xE w s k) ≤ XW w r0 + L ∧
      ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) < (N : ℝ) / 400} ≤
      ENNReal.ofReal (Real.exp (11 * B + 3 * L + 4 * ((N : ℝ) / 400)) * (3 / 160) ^ (N - 1)) := by
  have h := cubeM_chernoff_three (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => hs0) (fun _ => hs1) univ (faR1f x) (faR1f_meas x)
    ![B, L, (N : ℝ) / 400] ![11, 3, 4] (fun k _ => by fin_cases k <;> norm_num) (fun _ => Set.univ)
    (fun _ => MeasurableSet.univ)
  refine (measure_mono ?_).trans (h.trans ?_)
  · rintro w ⟨hw, hT, hL, hD⟩
    refine ⟨fun _ => Set.mem_univ _, fun k _ => ?_⟩
    fin_cases k
    · simpa [faR1f, XW] using hT
    · simp only [faR1f, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_add_distrib]
      have : ∑ i, Real.log (clamp01 (w r0 i)) = -XW w r0 := by unfold XW; simp
      rw [this]; unfold xE at hL; linarith
    · have := fa_Dsum_eq hw r0 x
      have e : ∑ i, faR1f x 2 i (w r0 i, w (flipAt x r0) i, w s i) =
          ∑ i, faR1f x 2 i (w r0 i, w (flipAt x r0) i, 0) := by
        refine sum_congr rfl fun i _ => ?_
        simp [faR1f]
      simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [e, this]; exact hD.le
  · have hsum : ∑ k ∈ (univ : Finset (Fin 3)), (![11, 3, 4] : Fin 3 → ℝ) k * ![B, L, (N : ℝ) / 400] k =
        11 * B + 3 * L + 4 * ((N : ℝ) / 400) := by
      simp [Fin.sum_univ_three]
    rw [hsum, ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    -- per-column factors
    have hl : Measurable fun v : ℝ => Real.log (clamp01 v) := Real.measurable_log.comp clamp01_measurable
    have hf : Measurable fun v : ℝ => Real.log (max (clamp01 v) (1 - clamp01 v)) :=
      Real.measurable_log.comp (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
    refine fa_prod_except x _ (a := 3 / 160) (b := 1) (by norm_num) le_rfl ?_ ?_
    · intro i hi
      have e : ∀ y u v, -∑ k ∈ (univ : Finset (Fin 3)), (![11, 3, 4] : Fin 3 → ℝ) k * faR1f x k i (y, u, v) =
          ((4 : ℕ) : ℝ) * Real.log (clamp01 y) + ((4 : ℕ) : ℝ) * Real.log (clamp01 u) +
            ((3 : ℕ) : ℝ) * Real.log (max (clamp01 v) (1 - clamp01 v)) := by
        intro y u v
        simp only [Fin.sum_univ_three, faR1f, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, if_neg hi]
        push_cast; ring
      simp_rw [e]
      rw [fa_triple_fact _ _ _ (hl.const_mul _) (hl.const_mul _) (hf.const_mul _), fa_lint_pow_log,
        fa_lint_fold_log, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    · have e : ∀ y u v, -∑ k ∈ (univ : Finset (Fin 3)), (![11, 3, 4] : Fin 3 → ℝ) k * faR1f x k x (y, u, v) =
          ((8 : ℕ) : ℝ) * Real.log (clamp01 y) + ((0 : ℕ) : ℝ) * Real.log (clamp01 u) +
            ((3 : ℕ) : ℝ) * Real.log (max (clamp01 v) (1 - clamp01 v)) := by
        intro y u v
        simp only [Fin.sum_univ_three, faR1f, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, if_pos rfl]
        push_cast; ring
      simp_rw [e]
      rw [fa_triple_fact _ _ _ (hl.const_mul _) (hl.const_mul _) (hf.const_mul _), fa_lint_pow_log,
        fa_lint_pow_log, fa_lint_fold_log, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      norm_num

/-- **Core bound, self case** (any third row `rc ∉ {r0, r0^x}`; no link). -/
theorem fa_r1_core_self (r0 rc : State N) (x : Fin N) (h0 : r0 ≠ rc) (h1 : flipAt x r0 ≠ rc) (B : ℝ) :
    cubeM N {w | w ∈ openCube N ∧ XW w r0 ≤ B ∧
      ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) < (N : ℝ) / 400} ≤
      ENNReal.ofReal (Real.exp (11 * B + 4 * ((N : ℝ) / 400)) * (1 / 40) ^ (N - 1)) := by
  have h := cubeM_chernoff_three (fun _ => r0) (fun _ => flipAt x r0) (fun _ => rc)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => h0) (fun _ => h1) {0, 2} (faR1f x) (faR1f_meas x)
    ![B, 0, (N : ℝ) / 400] ![11, 0, 4] (fun k _ => by fin_cases k <;> norm_num) (fun _ => Set.univ)
    (fun _ => MeasurableSet.univ)
  refine (measure_mono ?_).trans (h.trans ?_)
  · rintro w ⟨hw, hT, hD⟩
    refine ⟨fun _ => Set.mem_univ _, fun k hk => ?_⟩
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl
    · simpa [faR1f, XW] using hT
    · have := fa_Dsum_eq hw r0 x
      have e : ∑ i, faR1f x 2 i (w r0 i, w (flipAt x r0) i, w rc i) =
          ∑ i, faR1f x 2 i (w r0 i, w (flipAt x r0) i, 0) := by
        refine sum_congr rfl fun i _ => ?_
        simp [faR1f]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [e, this]; exact hD.le
  · have hsum : ∑ k ∈ ({0, 2} : Finset (Fin 3)), (![11, 0, 4] : Fin 3 → ℝ) k * ![B, 0, (N : ℝ) / 400] k =
        11 * B + 4 * ((N : ℝ) / 400) := by
      rw [sum_pair (by decide)]; simp
    rw [hsum, ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    have hl : Measurable fun v : ℝ => Real.log (clamp01 v) := Real.measurable_log.comp clamp01_measurable
    refine fa_prod_except x _ (a := 1 / 40) (b := 1) (by norm_num) le_rfl ?_ ?_
    · intro i hi
      have e : ∀ y u v, -∑ k ∈ ({0, 2} : Finset (Fin 3)), (![11, 0, 4] : Fin 3 → ℝ) k * faR1f x k i (y, u, v) =
          ((7 : ℕ) : ℝ) * Real.log (clamp01 y) + ((4 : ℕ) : ℝ) * Real.log (clamp01 u) + 0 := by
        intro y u v
        rw [sum_pair (by decide)]
        simp only [faR1f, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, if_neg hi]
        push_cast; ring
      simp_rw [e]
      rw [fa_triple_fact _ _ (fun _ => (0 : ℝ)) (hl.const_mul _) (hl.const_mul _) measurable_const,
        fa_lint_pow_log, fa_lint_pow_log, ← ENNReal.ofReal_mul (by norm_num)]
      simp only [Real.exp_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
      norm_num
    · have e : ∀ y u v, -∑ k ∈ ({0, 2} : Finset (Fin 3)), (![11, 0, 4] : Fin 3 → ℝ) k * faR1f x k x (y, u, v) =
          ((11 : ℕ) : ℝ) * Real.log (clamp01 y) + 0 + 0 := by
        intro y u v
        rw [sum_pair (by decide)]
        simp only [faR1f, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, if_pos rfl]
        push_cast; ring
      simp_rw [e]
      rw [fa_triple_fact _ (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (hl.const_mul _) measurable_const
        measurable_const, fa_lint_pow_log]
      simp only [Real.exp_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_le_one.2 (by norm_num)

end

end Census
end IIT
