/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: expectation bounds for the small-cut losses.

A "half reading" `φ` is `clamp01` or `1 - clamp01` (law of a generic row's reading of one unit).
* `colLawG_pos_part_le` : `E max((a + Σ_{r ∈ RG} φ_r(c r))/2^k - F, 0) ≤ max(μ, 0) + σ/2`,
  `μ = (a + |RG|/2)/2^k - F`, whenever `|RG|/(12·4^k) ≤ σ²` (mean + half a standard deviation);
* `unif_pos_part_half` : `E max(φ(v) - c, 0) = (1 - c)²/2` for `c ∈ [0,1]` (one generic row).
-/
import IIT.Census.B1UnivCols

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

variable {N : ℕ}

/-- A half reading. -/
def IsHalf (φ : ℝ → ℝ) : Prop := (∀ v, φ v = clamp01 v) ∨ (∀ v, φ v = 1 - clamp01 v)

lemma IsHalf.meas {φ : ℝ → ℝ} (h : IsHalf φ) : Measurable φ := by
  rcases h with h | h
  · rw [funext h]; exact clamp01_measurable
  · rw [funext h]; exact measurable_const.sub clamp01_measurable

lemma IsHalf.mem {φ : ℝ → ℝ} (h : IsHalf φ) (v : ℝ) : φ v ∈ Set.Icc (0 : ℝ) 1 := by
  rcases h with h | h <;> rw [h v]
  · exact ⟨clamp01_nonneg v, clamp01_le_one v⟩
  · exact ⟨by linarith [clamp01_le_one v], by linarith [clamp01_nonneg v]⟩

lemma IsHalf.int {φ : ℝ → ℝ} (h : IsHalf φ) : ∫ v, φ v ∂unif = 1 / 2 := by
  rcases h with h | h <;> simp_rw [h]
  · exact integral_clamp
  · exact integral_one_sub_clamp

lemma IsHalf.int_sq {φ : ℝ → ℝ} (h : IsHalf φ) : ∫ v, (φ v - 1 / 2) ^ 2 ∂unif = 1 / 12 := by
  have h2 := integral_cl_pow 2
  norm_num at h2
  have hi : Integrable clamp01 unif :=
    integrable_of_mem01 clamp01_measurable fun v => ⟨clamp01_nonneg v, clamp01_le_one v⟩
  have hi2 : Integrable (fun v => clamp01 v ^ 2) unif :=
    integrable_of_mem01 (clamp01_measurable.pow_const 2) fun v =>
      ⟨sq_nonneg _, by nlinarith [clamp01_nonneg v, clamp01_le_one v]⟩
  have e : ∀ v, (φ v - 1 / 2) ^ 2 = clamp01 v ^ 2 - clamp01 v + 1 / 4 := fun v => by
    rcases h with h | h <;> rw [h v] <;> ring
  simp_rw [e]
  have hA : Integrable (fun v => clamp01 v ^ 2 - clamp01 v) unif := hi2.sub hi
  rw [integral_add hA (integrable_const _), integral_sub hi2 hi, h2, integral_clamp, integral_const]
  norm_num

/-- **Mean plus half a standard deviation.** -/
theorem colLawG_pos_part_le (A : Finset (State N)) (RG : Finset {r // r ∉ A})
    (φ : {r // r ∉ A} → ℝ → ℝ) (hφ : ∀ r, IsHalf (φ r)) (a F σ : ℝ) (k : ℕ) (hσ : 0 < σ)
    (hvar : (RG.card : ℝ) / (12 * 4 ^ k) ≤ σ ^ 2) :
    ∫ c, max ((a + ∑ r ∈ RG, φ r (c r)) / 2 ^ k - F) 0 ∂colLawG A ≤
      max ((a + RG.card / 2) / 2 ^ k - F) 0 + σ / 2 := by
  classical
  set ψ : {r // r ∉ A} → ℝ → ℝ := fun r v => φ r v - 1 / 2 with hψ
  have hψm : ∀ r, Measurable (ψ r) := fun r => (hφ r).meas.sub measurable_const
  have hψb : ∀ r v, |ψ r v| ≤ 1 / 2 := fun r v => by
    have := (hφ r).mem v; rw [abs_le]; constructor <;> simp only [hψ] <;> linarith [this.1, this.2]
  have hψi : ∀ r, ∫ v, ψ r v ∂unif = 0 := fun r => by
    simp only [hψ]
    rw [integral_sub (integrable_of_mem01 (hφ r).meas (hφ r).mem) (integrable_const _), (hφ r).int,
      integral_const]; norm_num
  have hψ2 : ∀ r, ∫ v, ψ r v * ψ r v ∂unif = 1 / 12 := fun r => by
    simp only [hψ, ← sq]; exact (hφ r).int_sq
  set X : ({r // r ∉ A} → ℝ) → ℝ := fun c => ∑ r ∈ RG, ψ r (c r) with hX
  set μ := (a + RG.card / 2) / 2 ^ k - F with hμ
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hsplit : ∀ c, (a + ∑ r ∈ RG, φ r (c r)) / 2 ^ k - F = μ + X c / 2 ^ k := fun c => by
    simp only [hX, hμ, hψ, sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  -- integrability
  have hXm : Measurable X := Finset.measurable_sum _ fun r _ => (hψm r).comp (measurable_pi_apply r)
  have hXb : ∀ c, |X c| ≤ RG.card / 2 := fun c => by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ RG, |ψ r (c r)| ≤ ∑ _r ∈ RG, (1 / 2 : ℝ) := sum_le_sum fun r _ => hψb r _
      _ = RG.card / 2 := by rw [sum_const, nsmul_eq_mul]; ring
  have hXi : Integrable X (colLawG A) :=
    Integrable.of_bound hXm.aestronglyMeasurable (RG.card / 2) (ae_of_all _ fun c => by
      rw [Real.norm_eq_abs]; exact hXb c)
  have hX2i : Integrable (fun c => X c ^ 2) (colLawG A) :=
    Integrable.of_bound (hXm.pow_const 2).aestronglyMeasurable ((RG.card / 2) ^ 2) (ae_of_all _ fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := hXb c
      nlinarith [abs_nonneg (X c), sq_abs (X c)])
  -- moments of `X`
  have hint1 : ∀ r, Integrable (fun c : {r // r ∉ A} → ℝ => ψ r (c r)) (colLawG A) := fun r =>
    Integrable.of_bound ((hψm r).comp (measurable_pi_apply r)).aestronglyMeasurable
      (1 / 2) (ae_of_all _ fun c => by rw [Real.norm_eq_abs]; exact hψb r _)
  have hEX : ∫ c, X c ∂colLawG A = 0 := by
    simp only [hX]
    rw [integral_finset_sum RG fun r _ => hint1 r]
    refine sum_eq_zero fun r _ => ?_
    unfold colLawG
    rw [integral_pi_eval unif (hψm r).aestronglyMeasurable r, hψi r]
  have hEX2 : ∫ c, X c ^ 2 ∂colLawG A = RG.card / 12 := by
    have e : ∀ c, X c ^ 2 = ∑ r ∈ RG, ∑ r' ∈ RG, ψ r (c r) * ψ r' (c r') := fun c => by
      simp only [hX, sq, sum_mul_sum]
    simp_rw [e]
    have hint2 : ∀ r r', Integrable (fun c : {r // r ∉ A} → ℝ => ψ r (c r) * ψ r' (c r')) (colLawG A) :=
      fun r r' => Integrable.of_bound
        (((hψm r).comp (measurable_pi_apply r)).mul ((hψm r').comp (measurable_pi_apply r'))).aestronglyMeasurable
        (1 / 4) (ae_of_all _ fun c => by
          rw [Real.norm_eq_abs, abs_mul]
          have h1 := hψb r (c r); have h2 := hψb r' (c r')
          nlinarith [abs_nonneg (ψ r (c r)), abs_nonneg (ψ r' (c r'))])
    rw [integral_finset_sum _ fun r _ => integrable_finset_sum _ fun r' _ => hint2 r r']
    have hterm : ∀ r ∈ RG, ∫ c, ∑ r' ∈ RG, ψ r (c r) * ψ r' (c r') ∂colLawG A = 1 / 12 := by
      intro r hr
      rw [integral_finset_sum _ fun r' _ => hint2 r r', ← add_sum_erase _ _ hr]
      have hdiag : ∫ c, ψ r (c r) * ψ r (c r) ∂colLawG A = 1 / 12 := by
        unfold colLawG
        rw [integral_pi_eval unif (g := fun v => ψ r v * ψ r v) ((hψm r).mul (hψm r)).aestronglyMeasurable r,
          hψ2 r]
      rw [hdiag]
      have hoff : ∑ r' ∈ RG.erase r, ∫ c, ψ r (c r) * ψ r' (c r') ∂colLawG A = 0 := by
        refine sum_eq_zero fun r' hr' => ?_
        have hne : r ≠ r' := fun h => (ne_of_mem_erase hr') h.symm
        unfold colLawG
        rw [integral_pi_mul_of_ne unif hne (hψm r) (hψm r'), hψi r, zero_mul]
      rw [hoff, add_zero]
    rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]; ring
  -- the pointwise bound
  have hpt : ∀ c, max ((a + ∑ r ∈ RG, φ r (c r)) / 2 ^ k - F) 0 ≤
      max μ 0 + (X c / 2 ^ k / 2 + ((X c / 2 ^ k) ^ 2 / σ + σ) / 4) := by
    intro c
    rw [hsplit]
    have h1 : max (μ + X c / 2 ^ k) 0 ≤ max μ 0 + max (X c / 2 ^ k) 0 := by
      refine max_le ?_ (by positivity)
      linarith [le_max_left μ 0, le_max_left (X c / 2 ^ k) 0]
    have h2 : max (X c / 2 ^ k) 0 ≤ X c / 2 ^ k / 2 + ((X c / 2 ^ k) ^ 2 / σ + σ) / 4 := by
      set z := X c / 2 ^ k
      have hz : |z| ≤ (z ^ 2 / σ + σ) / 2 := by
        have h0 : (|z| - σ) ^ 2 ≥ 0 := sq_nonneg _
        have e : (z ^ 2 / σ + σ) / 2 = (z ^ 2 + σ ^ 2) / (2 * σ) := by field_simp
        rw [e, le_div_iff₀ (by positivity)]
        nlinarith [sq_abs z]
      rcases le_total z 0 with hz0 | hz0
      · rw [max_eq_right hz0]; rw [abs_of_nonpos hz0] at hz; linarith
      · rw [max_eq_left hz0]; rw [abs_of_nonneg hz0] at hz; linarith
    linarith
  set C2 : ℝ := 1 / (4 * 4 ^ k * σ) with hC2
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have hpt' : ∀ c, max ((a + ∑ r ∈ RG, φ r (c r)) / 2 ^ k - F) 0 ≤
      (max μ 0 + σ / 4) + 1 / (2 * 2 ^ k) * X c + C2 * X c ^ 2 := by
    intro c
    have := hpt c
    have e : X c / 2 ^ k / 2 + ((X c / 2 ^ k) ^ 2 / σ + σ) / 4 =
        σ / 4 + 1 / (2 * 2 ^ k) * X c + C2 * X c ^ 2 := by
      rw [hC2, div_pow, show ((2 : ℝ) ^ k) ^ 2 = 4 ^ k by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      field_simp; ring
    linarith
  have hB1 : Integrable (fun c => (max μ 0 + σ / 4) + 1 / (2 * 2 ^ k) * X c) (colLawG A) :=
    (integrable_const _).add (hXi.const_mul _)
  have hB2 : Integrable (fun c => C2 * X c ^ 2) (colLawG A) := hX2i.const_mul _
  have hB : Integrable (fun c => (max μ 0 + σ / 4) + 1 / (2 * 2 ^ k) * X c + C2 * X c ^ 2) (colLawG A) :=
    hB1.add hB2
  have hLi : Integrable (fun c => max ((a + ∑ r ∈ RG, φ r (c r)) / 2 ^ k - F) 0) (colLawG A) := by
    refine Integrable.of_bound ?_ (|μ| + RG.card / 2 / 2 ^ k) (ae_of_all _ fun c => ?_)
    · exact (((measurable_const.add (Finset.measurable_sum _ fun r _ =>
        (hφ r).meas.comp (measurable_pi_apply r))).div_const _).sub_const _).max
        measurable_const |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), hsplit]
      refine max_le ?_ (by positivity)
      have := hXb c
      have h3 : X c / 2 ^ k ≤ RG.card / 2 / 2 ^ k := div_le_div_of_nonneg_right (le_of_abs_le this) h2k.le
      linarith [le_abs_self μ]
  refine (integral_mono hLi hB hpt').trans ?_
  have e1 := integral_add hB1 hB2
  have e2 := integral_add (integrable_const (max μ 0 + σ / 4)) (hXi.const_mul (1 / (2 * 2 ^ k))) (μ := colLawG A)
  rw [e1, e2, integral_const_mul, integral_const_mul, hEX, hEX2, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
  have hq : C2 * (RG.card / 12) ≤ σ / 4 := by
    rw [hC2]
    have := hvar
    rw [div_le_iff₀ (by positivity)] at this
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### One generic row: the exact value -/

lemma unif_eq_interval {f : ℝ → ℝ} (hf : ∀ v ∈ Set.Icc (0 : ℝ) 1, f (clamp01 v) = f v) :
    ∫ v, f (clamp01 v) ∂unif = ∫ v in (0 : ℝ)..1, f v := by
  unfold unif
  rw [setIntegral_congr_fun measurableSet_Icc (g := f) (fun v hv => hf v hv),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

lemma interval_pos_part {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ v in (0 : ℝ)..1, max (v - c) 0 = (1 - c) ^ 2 / 2 := by
  have hcont : Continuous fun v : ℝ => max (v - c) 0 := (continuous_id.sub continuous_const).max continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ v in (0 : ℝ)..c, max (v - c) 0 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun v hv => by
      rw [Set.uIcc_of_le hc0] at hv; exact max_eq_right (by linarith [hv.2])]
    simp
  have h2 : ∫ v in c..1, max (v - c) 0 = ∫ v in c..1, (v - c) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hc1] at hv; exact max_eq_left (by linarith [hv.1])
  rw [h1, h2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp; ring

lemma interval_pos_part' {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ v in (0 : ℝ)..1, max (1 - v - c) 0 = (1 - c) ^ 2 / 2 := by
  have h := intervalIntegral.integral_comp_sub_left (fun v => max (v - c) 0) (a := 0) (b := 1) 1
  simp only [sub_self, sub_zero] at h
  have e : ∀ v : ℝ, max (1 - v - c) 0 = max ((1 - v) - c) 0 := fun v => rfl
  rw [show (fun v : ℝ => max (1 - v - c) 0) = fun v => max ((1 - v) - c) 0 from rfl, h,
    interval_pos_part hc0 hc1]

/-- **One generic row**: `E max(φ(v) - c, 0) = (1 - c)²/2`. -/
theorem unif_pos_part_half {φ : ℝ → ℝ} (hφ : IsHalf φ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ v, max (φ v - c) 0 ∂unif = (1 - c) ^ 2 / 2 := by
  rcases hφ with h | h <;> simp_rw [h]
  · rw [unif_eq_interval (f := fun v => max (v - c) 0) fun v hv => by rw [clamp01_of_mem hv]]
    exact interval_pos_part hc0 hc1
  · rw [unif_eq_interval (f := fun v => max (1 - v - c) 0) fun v hv => by rw [clamp01_of_mem hv]]
    exact interval_pos_part' hc0 hc1

end Census
end IIT
