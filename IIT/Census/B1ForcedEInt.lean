/-
Census, B1 forced leaf 17 (`joint_x2`, agent "forcedE"), part 1: the `Neg`-region integral.

For the cause regime at `(r0, x)` the unit `j` is in `NegX` iff `(27/25) y ≤ u` (`y = y_{r0,j}`,
`u = y_{r0^x,j}`).  On that region the V-term integrand of the RS template is at least
`((y+u)/(2y))^λ`, whose `u`-integral over `[ρ y, 1]` (`ρ = 27/25`) is the closed form `bX λ y`; `bX ≤ gX`.
The outer integral `∫_{v⁴}^{q⁴} y^{P/4} bX λ y dy` is the computable rational `bIq v q λ P`.
-/
import IIT.Census.B1RegInt

namespace IIT
namespace Census

open Finset MeasureTheory

/-- `∫_{ρy}^1 ((y+u)/(2y))^λ du` in closed form, `ρ = 27/25` (so `y + ρ y = (52/25) y`). -/
noncomputable def bX (lam : ℕ) (y : ℝ) : ℝ :=
  ((1 + y) ^ (lam + 1) - (52 / 25 * y) ^ (lam + 1)) / ((lam + 1) * (2 * y) ^ lam)

/-- **The `Neg`-region integral.** -/
theorem integral_negPart (lam : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ u in (27 / 25 * y)..1, ((y + u) / (2 * y)) ^ lam = bX lam y := by
  have h2y : (2 * y) ^ lam ≠ 0 := pow_ne_zero _ (by positivity)
  have e1 : ∀ u : ℝ, ((y + u) / (2 * y)) ^ lam = (1 / (2 * y) ^ lam) * (y + u) ^ lam := fun u => by
    rw [div_pow]; ring
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_left (fun x => x ^ lam) y,
    integral_pow]
  unfold bX
  have : y + 27 / 25 * y = 52 / 25 * y := by ring
  rw [this, add_comm y 1]
  have hl : ((lam : ℝ) + 1) ≠ 0 := by positivity
  field_simp

lemma bX_nonneg (lam : ℕ) {y : ℝ} (hy : 0 < y) (hr : 27 / 25 * y ≤ 1) : 0 ≤ bX lam y := by
  rw [← integral_negPart lam hy]
  exact intervalIntegral.integral_nonneg hr fun u hu => pow_nonneg (div_nonneg (by linarith [hu.1]) (by positivity)) _

/-- **`bX ≤ gX`** (the `Neg` part of the V-integrand is part of the full integrand). -/
theorem bX_le_gX (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c)
    (hr : 27 / 25 * y ≤ 1) : bX lam y ≤ gX lam c y := by
  rw [← integral_negPart lam hy, ← integral_maxpow lam hy hy1 hc hcy]
  set F : ℝ → ℝ := fun u => (max ((y + u) / (2 * y)) (min 1 (c / y))) ^ lam
  have hFc : Continuous F := by
    simp only [F]
    have : Continuous fun u : ℝ => (y + u) / (2 * y) := by fun_prop
    exact (this.max continuous_const).pow _
  have h0r : 0 ≤ 27 / 25 * y := by positivity
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable 0 (27 / 25 * y))
    (hFc.intervalIntegrable _ 1)]
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..(27 / 25 * y), F u :=
    intervalIntegral.integral_nonneg h0r fun u hu => pow_nonneg
      (le_trans (le_min zero_le_one (div_nonneg hc.le hy.le)) (le_max_right _ _)) _
  have hmono : ∫ u in (27 / 25 * y)..1, ((y + u) / (2 * y)) ^ lam ≤ ∫ u in (27 / 25 * y)..1, F u := by
    refine intervalIntegral.integral_mono_on hr ((by fun_prop : Continuous fun u : ℝ =>
      ((y + u) / (2 * y)) ^ lam).intervalIntegrable _ _) (hFc.intervalIntegrable _ _) fun u hu => ?_
    exact pow_le_pow_left₀ (div_nonneg (by linarith [hu.1]) (by positivity)) (le_max_left _ _) _
  linarith

/-- Pointwise: `y^p · bX` as a combination of real powers. -/
lemma rpow_mul_bX (lam : ℕ) {y p : ℝ} (hy : 0 < y) :
    y ^ p * bX lam y =
      (∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          y ^ (p + k - lam)) -
        (52 / 25 : ℝ) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam) * y ^ (p + 1) := by
  have hpow : ∀ e : ℝ, ∀ k : ℕ, y ^ (e + k - lam) = y ^ e * y ^ k / y ^ lam := fun e k => by
    rw [Real.rpow_sub hy, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_natCast]
  unfold bX
  rw [← binS_eq, binS, Real.rpow_add hy, Real.rpow_one]
  simp only [hpow]
  have hyl : y ^ lam ≠ 0 := pow_ne_zero _ hy.ne'
  have hl : (lam : ℝ) + 1 ≠ 0 := by positivity
  rw [sub_div, mul_sub, Finset.sum_div, Finset.mul_sum]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [mul_pow]
    field_simp
  · rw [mul_pow, mul_pow]
    field_simp
    ring

/-- **The exact outer `Neg` integral.** -/
theorem integral_bX (lam : ℕ) {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hk : ∀ k ∈ range (lam + 2), p + k - lam ≠ -1) (hp : p + 1 ≠ -1) :
    ∫ y in a..b, y ^ p * bX lam y =
      (∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          powInt a b (p + k - lam)) -
        (52 / 25 : ℝ) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam) * powInt a b (p + 1) := by
  have heq : Set.EqOn (fun y => y ^ p * bX lam y) (fun y =>
      (∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          y ^ (p + k - lam)) -
        (52 / 25 : ℝ) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam) * y ^ (p + 1)) (Set.uIcc a b) :=
    fun y hy => by
      rw [Set.uIcc_of_le hab] at hy
      exact rpow_mul_bX lam (lt_of_lt_of_le ha hy.1)
  have hI : ∀ q : ℝ, IntervalIntegrable (fun y : ℝ => y ^ q) MeasureTheory.volume a b :=
    fun q => rpow_intervalIntegrable ha hab
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_sub,
    intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
    rw [integral_rpow_pos ha hab hp]
    congr 1
    exact sum_congr rfl fun k hkm => by rw [integral_rpow_pos ha hab (hk k hkm)]; rfl
  · exact fun k _ => (hI _).const_mul _
  · exact sum_rpow_intervalIntegrable ha hab _ _ _
  · exact (hI _).const_mul _

/-- The computable value of `∫_{v⁴}^{q⁴} y^{P/4} bX λ y dy`. -/
def bIq (v q : ℚ) (lam P : ℕ) : ℚ :=
  let a : ℚ := 1 / ((lam + 1) * 2 ^ lam)
  (∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℚ) * a * powIntQ v q ((P : ℤ) + 4 * k - 4 * lam + 4)) -
    (52 / 25 : ℚ) ^ (lam + 1) * a * powIntQ v q ((P : ℤ) + 8)

/-- **`bIq` is the outer `Neg` integral.** -/
theorem bIq_eq (v q : ℚ) (hv : 0 < v) (hvq : v ≤ q) (lam P : ℕ)
    (hk : ∀ k ∈ range (lam + 2), (P : ℤ) + 4 * k - 4 * lam + 4 ≠ 0) (hp : (P : ℤ) + 8 ≠ 0) :
    ((bIq v q lam P : ℚ) : ℝ) = ∫ y in ((v : ℝ) ^ 4)..((q : ℝ) ^ 4), y ^ ((P : ℝ) / 4) * bX lam y := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hq0 : 0 < q := lt_of_lt_of_le hv hvq
  have hvq' : (v : ℝ) ^ 4 ≤ (q : ℝ) ^ 4 := pow_le_pow_left₀ hv'.le (by exact_mod_cast hvq) 4
  have hkR : ∀ k ∈ range (lam + 2), (P : ℝ) / 4 + k - lam ≠ -1 := fun k hkm h => by
    apply hk k hkm; have : (((P : ℤ) + 4 * k - 4 * lam + 4 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hpR : (P : ℝ) / 4 + 1 ≠ -1 := fun h => hp (by
    have : (((P : ℤ) + 8 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this)
  rw [integral_bX lam (by positivity) hvq' hkR hpR]
  rw [show powInt ((v : ℝ) ^ 4) ((q : ℝ) ^ 4) ((P : ℝ) / 4 + 1) =
      ((powIntQ v q ((P : ℤ) + 8) : ℚ) : ℝ) from
    (powIntQ_cast hv hq0 ((P : ℤ) + 8) (by push_cast; ring)).symm]
  rw [sum_congr rfl fun k _ => show ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
      powInt ((v : ℝ) ^ 4) ((q : ℝ) ^ 4) ((P : ℝ) / 4 + k - lam) =
      ((((lam + 1).choose k : ℚ) * (1 / ((lam + 1) * 2 ^ lam)) *
        powIntQ v q ((P : ℤ) + 4 * k - 4 * lam + 4) : ℚ) : ℝ) from by
    rw [← powIntQ_cast hv hq0 ((P : ℤ) + 4 * k - 4 * lam + 4) (by push_cast; ring)]
    push_cast; ring]
  unfold bIq
  push_cast
  ring

end Census
end IIT
