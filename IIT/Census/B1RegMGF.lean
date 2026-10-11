/-
Census, module D1' part 1 (Lemma RS, W9 §4.1): the per-unit moment generating function of the regime-X
V-variable, in closed form (W7 §2.1).

For `λ ∈ ℕ`, `y ∈ (0, 1]` and a cap level `c ∈ [y/2, 1]`:

  `E_{U ~ unif} exp(-λ · min(log(2y/(y+U)), max(0, log(y/c)))) = gX λ c y`,
  `gX λ c y = u*·m^λ + ((1+y)^{λ+1} - (2 min(y,c))^{λ+1}) / ((λ+1)(2y)^λ)`,

with `m = min(1, c/y)` and `u* = 2 min(y, c) - y`. The integrand equals `max((y+U)/(2y), m)^λ`: it is the
constant `m^λ` below `u*` and `((y+U)/(2y))^λ` above.
-/
import IIT.Census.B1Chernoff

namespace IIT
namespace Census

open MeasureTheory Set intervalIntegral

/-- The closed form of the per-unit MGF (W7 §2.1). -/
noncomputable def gX (lam : ℕ) (c y : ℝ) : ℝ :=
  (2 * min y c - y) * (min 1 (c / y)) ^ lam +
    ((1 + y) ^ (lam + 1) - (2 * min y c) ^ (lam + 1)) / ((lam + 1) * (2 * y) ^ lam)

/-- The integrand, pointwise: `exp(-λ min(A, B)) = max((y+u)/(2y), m)^λ`. -/
lemma mgfX_pointwise (lam : ℕ) {c y u : ℝ} (hy : 0 < y) (hc : 0 < c) (hu : 0 ≤ u) :
    Real.exp (-(lam : ℝ) * min (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c)))) =
      (max ((y + u) / (2 * y)) (min 1 (c / y))) ^ lam := by
  have hyu : 0 < y + u := by linarith
  have h1 : 0 < (y + u) / (2 * y) := by positivity
  have h2 : 0 < min 1 (c / y) := lt_min one_pos (div_pos hc hy)
  -- log of the two candidates
  have hA : Real.log ((y + u) / (2 * y)) = -Real.log (2 * y / (y + u)) := by
    rw [← Real.log_inv, inv_div]
  have hB : Real.log (min 1 (c / y)) = -max 0 (Real.log (y / c)) := by
    rcases le_total 1 (c / y) with h | h
    · rw [min_eq_left h, Real.log_one, max_eq_left, neg_zero]
      rw [Real.log_nonpos_iff (div_pos hy hc).le]
      rw [div_le_one hc]; rwa [le_div_iff₀ hy, one_mul] at h
    · rw [min_eq_right h, max_eq_right, ← Real.log_inv, inv_div]
      apply Real.log_nonneg
      rw [le_div_iff₀ hc, one_mul]; rwa [div_le_one hy] at h
  have hlogmax : Real.log (max ((y + u) / (2 * y)) (min 1 (c / y))) =
      max (Real.log ((y + u) / (2 * y))) (Real.log (min 1 (c / y))) := by
    rcases le_total ((y + u) / (2 * y)) (min 1 (c / y)) with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_le_log h1 h)]
    · rw [max_eq_left h, max_eq_left (Real.log_le_log h2 h)]
  rw [← Real.exp_log (lt_max_of_lt_left h1 : 0 < max ((y + u) / (2 * y)) (min 1 (c / y))),
    ← Real.exp_nat_mul, hlogmax, hA, hB, max_neg_neg]
  ring_nf

/-- The integral of the max form: flat below `u*`, polynomial above. -/
lemma integral_maxpow (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    ∫ u in (0 : ℝ)..1, (max ((y + u) / (2 * y)) (min 1 (c / y))) ^ lam = gX lam c y := by
  set m := min 1 (c / y)
  set us := 2 * min y c - y with hus
  have hm : 2 * y * m = 2 * min y c := by
    simp only [m]
    rcases le_total y c with h | h
    · rw [min_eq_left h, min_eq_left ((one_le_div hy).2 h)]; ring
    · rw [min_eq_right h, min_eq_right ((div_le_one hy).2 h)]; field_simp
  have hus0 : 0 ≤ us := by
    simp only [us]; rcases le_total y c with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hus1 : us ≤ 1 := by
    simp only [us]; have := min_le_left y c; linarith
  have h2y : 0 < 2 * y := by linarith
  have hlo : EqOn (fun u => (max ((y + u) / (2 * y)) m) ^ lam) (fun _ => m ^ lam) (uIcc 0 us) := by
    intro u hu
    rw [uIcc_of_le hus0] at hu
    have : (y + u) / (2 * y) ≤ m := by
      rw [div_le_iff₀ h2y]; nlinarith [hu.2]
    simp only [max_eq_right this]
  have hhi : EqOn (fun u => (max ((y + u) / (2 * y)) m) ^ lam)
      (fun u => (u + y) ^ lam / (2 * y) ^ lam) (uIcc us 1) := by
    intro u hu
    rw [uIcc_of_le hus1] at hu
    have : m ≤ (y + u) / (2 * y) := by
      rw [le_div_iff₀ h2y]; nlinarith [hu.1]
    show (max ((y + u) / (2 * y)) m) ^ lam = (u + y) ^ lam / (2 * y) ^ lam
    rw [max_eq_left this, div_pow, add_comm y u]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => (max ((y + u) / (2 * y)) m) ^ lam) volume a b :=
    fun a b => (Continuous.intervalIntegrable (by fun_prop) a b)
  rw [← integral_add_adjacent_intervals (hint 0 us) (hint us 1), integral_congr hlo,
    integral_congr hhi, intervalIntegral.integral_const, intervalIntegral.integral_div, intervalIntegral.integral_comp_add_right
      (fun u => u ^ lam), integral_pow]
  simp only [smul_eq_mul, sub_zero, gX]
  have : us + y = 2 * min y c := by simp only [us]; ring
  rw [this]
  push_cast
  field_simp
  ring

/-- **The per-unit MGF of the regime-X V-variable** (W7 §2.1), as a lintegral under `unif`. -/
theorem lintegral_mgfX (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) *
        min (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c))))) ∂unif =
      ENNReal.ofReal (gX lam c y) := by
  have hpt : ∀ u ∈ Icc (0 : ℝ) 1, Real.exp (-(lam : ℝ) *
      min (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c)))) =
        (max ((y + u) / (2 * y)) (min 1 (c / y))) ^ lam :=
    fun u hu => mgfX_pointwise lam hy hc hu.1
  unfold unif
  rw [setLIntegral_congr_fun measurableSet_Icc (fun u hu => congrArg ENNReal.ofReal (hpt u hu))]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_maxpow lam hy hy1 hc hcy]
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · exact Filter.Eventually.of_forall fun u => by positivity

end Census
end IIT
