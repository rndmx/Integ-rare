/-
Elementary estimates for the Lyapunov CLT (`CLTProof.lean`): products of complex numbers of
norm `≤ 1`, the third-order Taylor bound for `exp (y I)`, and the second-order bound for
`exp (-w)`, `w ≥ 0`.  Imports only Mathlib.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential

namespace IIT
namespace Census

open Complex Finset

/-- `‖∏ a - ∏ b‖ ≤ ∑ ‖a - b‖` for factors of norm at most one. -/
lemma clt_norm_prod_sub_prod_le {α : Type*} (s : Finset α) (a b : α → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    have ha' : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj => ha j (mem_insert_of_mem hj)
    have hb' : ∀ j ∈ s, ‖b j‖ ≤ 1 := fun j hj => hb j (mem_insert_of_mem hj)
    have h1 := ih ha' hb'
    have hai := ha i (mem_insert_self i s)
    have hB : ‖∏ j ∈ s, b j‖ ≤ 1 := by
      rw [norm_prod]; exact prod_le_one (fun _ _ => norm_nonneg _) hb'
    calc ‖a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j‖
        = ‖a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j‖ := by
          congr 1; ring
      _ ≤ ‖a i‖ * ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ + ‖a i - b i‖ * ‖∏ j ∈ s, b j‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ 1 * ∑ j ∈ s, ‖a j - b j‖ + ‖a i - b i‖ * 1 := by
          gcongr
      _ = ‖a i - b i‖ + ∑ j ∈ s, ‖a j - b j‖ := by ring

/-- Third-order Taylor bound for `exp (y I)` (crude constant). -/
lemma clt_taylor3 (y : ℝ) :
    ‖exp ((y : ℂ) * I) - (1 + (y : ℂ) * I - (y : ℂ) ^ 2 / 2)‖ ≤ 4 * |y| ^ 3 := by
  have hn : ‖(y : ℂ) * I‖ = |y| := by simp
  rcases le_or_gt |y| 1 with h | h
  · have hb := Complex.exp_bound (x := (y : ℂ) * I) (by rw [hn]; exact h) (n := 3) (by norm_num)
    rw [hn] at hb
    have e : ∑ m ∈ range 3, ((y : ℂ) * I) ^ m / (m.factorial : ℂ)
        = 1 + (y : ℂ) * I - (y : ℂ) ^ 2 / 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast
      ring_nf; rw [I_sq]; ring
    rw [e] at hb
    refine hb.trans ?_
    have : (0 : ℝ) ≤ |y| ^ 3 := by positivity
    norm_num [Nat.factorial]
    nlinarith
  · have h1 : ‖exp ((y : ℂ) * I)‖ = 1 := by
      rw [mul_comm]; exact norm_exp_I_mul_ofReal y
    have hy2 : ‖(y : ℂ) ^ 2 / 2‖ = y ^ 2 / 2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; simp
    calc ‖exp ((y : ℂ) * I) - (1 + (y : ℂ) * I - (y : ℂ) ^ 2 / 2)‖
        ≤ ‖exp ((y : ℂ) * I)‖ + (‖(1 : ℂ)‖ + ‖(y : ℂ) * I‖ + ‖(y : ℂ) ^ 2 / 2‖) := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ = 2 + |y| + y ^ 2 / 2 := by rw [h1, hn, hy2]; simp; ring
      _ ≤ 4 * |y| ^ 3 := by
          have hy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
          rw [hy]; nlinarith

/-- `|y|³ ≤ δ y² + y⁴ / δ`. -/
lemma clt_cube_le (y : ℝ) {δ : ℝ} (hδ : 0 < δ) : |y| ^ 3 ≤ δ * y ^ 2 + y ^ 4 / δ := by
  have h2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have h4 : y ^ 4 = |y| ^ 4 := by rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
  rw [h2, h4]
  have ha := abs_nonneg y
  rcases le_or_gt |y| δ with h | h
  · have : |y| ^ 3 ≤ δ * |y| ^ 2 := by
      have : |y| ^ 3 = |y| * |y| ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h (by positivity)
    have : 0 ≤ |y| ^ 4 / δ := by positivity
    linarith
  · have : |y| ^ 3 ≤ |y| ^ 4 / δ := by
      rw [le_div_iff₀ hδ]
      have : |y| ^ 4 = |y| ^ 3 * |y| := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left h.le (by positivity)
    have : 0 ≤ δ * |y| ^ 2 := by positivity
    linarith

/-- `|exp (-w) - (1 - w)| ≤ w²` for `w ≥ 0`. -/
lemma clt_exp_neg_bound {w : ℝ} (hw : 0 ≤ w) : |Real.exp (-w) - (1 - w)| ≤ w ^ 2 := by
  rcases le_or_gt w 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (x := -w) (by rw [abs_neg, abs_of_nonneg hw]; exact h)
    have e : Real.exp (-w) - (1 - w) = Real.exp (-w) - 1 - -w := by ring
    rw [e]; simpa using this
  · have h1 : Real.exp (-w) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 0 < Real.exp (-w) := Real.exp_pos _
    rw [abs_le]; constructor <;> nlinarith

end Census
end IIT
