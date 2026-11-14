/-
Census of IIT 2.0: the constants `d0`, `d1` of Lemma 2 of the note, as integrals.
`d0 = ∫₀¹ 2u log₂(2u) du = 1 - 1/(2 ln 2)` and
`d1 = ∫₀¹∫₀¹ (u+v) log₂(u+v) dv du = 4/3 - 5/(6 ln 2)`.
-/
import Mathlib

namespace IIT2

open Real intervalIntegral

lemma continuous_sq_mul_log : Continuous fun t : ℝ => t ^ 2 * Real.log t := by
  have : (fun t : ℝ => t ^ 2 * Real.log t) = fun t => t * (t * Real.log t) := by
    funext t; ring
  rw [this]; exact continuous_id.mul Real.continuous_mul_log

lemma continuous_cube_mul_log : Continuous fun t : ℝ => t ^ 3 * Real.log t := by
  have : (fun t : ℝ => t ^ 3 * Real.log t) = fun t => t ^ 2 * (t * Real.log t) := by
    funext t; ring
  rw [this]; exact (continuous_pow 2).mul Real.continuous_mul_log

/-- `∫₀¹ 2u ln(2u) du = ln 2 - 1/2`. -/
theorem integral_d0 : ∫ u in (0 : ℝ)..1, 2 * u * Real.log (2 * u) = Real.log 2 - 1 / 2 := by
  have hF : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => u ^ 2 * Real.log (2 * u) - u ^ 2 / 2)
        (2 * x * Real.log (2 * x)) x := by
    intro x hx
    have hx0 : (2 * x) ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun u : ℝ => Real.log (2 * u)) (2 / (2 * x)) x := by
      have := ((hasDerivAt_id x).const_mul 2).log hx0
      simpa using this
    have h2 := ((hasDerivAt_pow 2 x).mul h1).sub ((hasDerivAt_pow 2 x).div_const 2)
    have hx' : x ≠ 0 := by linarith [hx.1]
    refine h2.congr_deriv ?_
    first | (field_simp; ring) | ring | (simp; field_simp; ring) | (simp; field_simp) | field_simp
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) ?_ hF ?_]
  · norm_num
  · have : (fun u : ℝ => u ^ 2 * Real.log (2 * u) - u ^ 2 / 2) =
        fun u => (1 / 4) * ((2 * u) ^ 2 * Real.log (2 * u)) - u ^ 2 / 2 := by
      funext u; ring
    rw [this]
    exact ((continuous_const.mul (continuous_sq_mul_log.comp (continuous_const.mul
      continuous_id))).sub ((continuous_pow 2).div_const 2)).continuousOn
  · have : (fun u : ℝ => 2 * u * Real.log (2 * u)) = fun u => (2 * u) * Real.log (2 * u) := rfl
    exact (Real.continuous_mul_log.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- `G(t) = t²/2 ln t - t²/4`, an antiderivative of `t ln t`. -/
noncomputable def Gd (t : ℝ) : ℝ := t ^ 2 / 2 * Real.log t - t ^ 2 / 4

/-- `H(t) = t³/6 ln t - 5t³/36`, an antiderivative of `G`. -/
noncomputable def Hd (t : ℝ) : ℝ := t ^ 3 / 6 * Real.log t - 5 * t ^ 3 / 36

lemma continuous_Gd : Continuous Gd := by
  have : Gd = fun t => (1 / 2) * (t ^ 2 * Real.log t) - t ^ 2 / 4 := by
    funext t; unfold Gd; ring
  rw [this]
  exact (continuous_const.mul continuous_sq_mul_log).sub ((continuous_pow 2).div_const 4)

lemma continuous_Hd : Continuous Hd := by
  have : Hd = fun t => (1 / 6) * (t ^ 3 * Real.log t) - 5 * t ^ 3 / 36 := by
    funext t; unfold Hd; ring
  rw [this]
  exact (continuous_const.mul continuous_cube_mul_log).sub
    ((continuous_const.mul (continuous_pow 3)).div_const 36)

lemma hasDerivAt_Gd {t : ℝ} (ht : 0 < t) : HasDerivAt Gd (t * Real.log t) t := by
  have h1 := Real.hasDerivAt_log ht.ne'
  have h2 := (((hasDerivAt_pow 2 t).div_const 2).mul h1).sub ((hasDerivAt_pow 2 t).div_const 4)
  unfold Gd
  refine h2.congr_deriv ?_
  have ht' : t ≠ 0 := ht.ne'
  first | (field_simp; ring) | ring | (simp; field_simp; ring) | field_simp

lemma hasDerivAt_Hd {t : ℝ} (ht : 0 < t) : HasDerivAt Hd (Gd t) t := by
  have h1 := Real.hasDerivAt_log ht.ne'
  have h2 := (((hasDerivAt_pow 3 t).div_const 6).mul h1).sub
    (((hasDerivAt_pow 3 t).const_mul 5).div_const 36)
  unfold Hd
  refine h2.congr_deriv ?_
  unfold Gd
  have ht' : t ≠ 0 := ht.ne'
  first | (field_simp; ring) | ring | (simp; field_simp; ring) | field_simp

/-- Inner integral: `∫₀¹ (u+v) ln(u+v) dv = G(u+1) - G(u)` for `u ≥ 0`. -/
lemma integral_inner (u : ℝ) (hu : 0 ≤ u) :
    ∫ v in (0 : ℝ)..1, (u + v) * Real.log (u + v) = Gd (u + 1) - Gd u := by
  have hF : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => Gd (u + v))
      ((u + x) * Real.log (u + x)) x := by
    intro x hx
    exact (hasDerivAt_Gd (show 0 < u + x by linarith [hx.1])).comp_const_add u x
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) ?_ hF ?_]
  · simp
  · exact (continuous_Gd.comp (continuous_const.add continuous_id)).continuousOn
  · exact (Real.continuous_mul_log.comp (continuous_const.add continuous_id)).intervalIntegrable _ _

lemma integral_Gd (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, Gd t = Hd b - Hd a :=
  integral_eq_sub_of_hasDerivAt_of_le hab continuous_Hd.continuousOn
    (fun x hx => hasDerivAt_Hd (by linarith [hx.1])) (continuous_Gd.intervalIntegrable _ _)

/-- `∫₀¹∫₀¹ (u+v) ln(u+v) dv du = (4/3) ln 2 - 5/6`. -/
theorem integral_d1 :
    ∫ u in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, (u + v) * Real.log (u + v)) =
      4 / 3 * Real.log 2 - 5 / 6 := by
  rw [integral_congr (g := fun u => Gd (u + 1) - Gd u) (fun u hu => by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact integral_inner u hu.1)]
  have hi1 : IntervalIntegrable (fun u => Gd (u + 1)) MeasureTheory.volume 0 1 :=
    (continuous_Gd.comp (continuous_id.add continuous_const)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hi1 (continuous_Gd.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_comp_add_right Gd 1]
  rw [integral_Gd _ _ (by norm_num) (by norm_num), integral_Gd _ _ (by norm_num) (by norm_num)]
  unfold Hd
  norm_num
  ring

/-- The constant `d0 = 1 - 1/(2 ln 2)` and the bound `d0 > 0.2786`. -/
lemma d0_gt : (2786 / 10000 : ℝ) < (Real.log 2 - 1 / 2) / Real.log 2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- `d1 = 4/3 - 5/(6 ln 2) < 0.1311`. -/
lemma d1_lt : (4 / 3 * Real.log 2 - 5 / 6) / Real.log 2 < (1311 / 10000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- For `m ≥ 2`: `1/(12 ln 2) < 0.1311`. -/
lemma var_bound_lt : (1 / 12 : ℝ) / Real.log 2 < 1311 / 10000 := by
  have h1 := Real.log_two_gt_d9
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

end IIT2
