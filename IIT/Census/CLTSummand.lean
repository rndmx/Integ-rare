/-
Lyapunov CLT, one summand: for a centred real random variable `Y` with a fourth moment,
`‖E exp(iY) - exp(-E Y² / 2)‖ ≤ 4 (δ E Y² + E Y⁴ / δ) + E Y⁴ / 4` for every `δ > 0`.
Imports only Mathlib (through `CLTCharFun`).
-/
import IIT.Census.CLTCharFun
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space

namespace IIT
namespace Census

open MeasureTheory Complex

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma clt_int_of_pow4 {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => Y ω ^ k) μ := by
  refine (h4.add (integrable_const (1 : ℝ))).mono' (hY.pow k)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have h4' : |Y ω| ^ 4 = Y ω ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  rcases le_or_gt |Y ω| 1 with h | h
  · have : |Y ω| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) h
    have : 0 ≤ Y ω ^ 4 := by positivity
    simp only [Pi.add_apply]; linarith
  · have : |Y ω| ^ k ≤ |Y ω| ^ 4 := pow_le_pow_right₀ h.le hk
    simp only [Pi.add_apply]; linarith

lemma clt_summand {Y : Ω → ℝ} (hY : Measurable Y)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) (h0 : ∫ ω, Y ω ∂μ = 0) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ ω, exp ((Y ω : ℂ) * I) ∂μ - exp (-((∫ ω, Y ω ^ 2 ∂μ : ℝ) : ℂ) / 2)‖
      ≤ 4 * (δ * ∫ ω, Y ω ^ 2 ∂μ + (∫ ω, Y ω ^ 4 ∂μ) / δ) + (∫ ω, Y ω ^ 4 ∂μ) / 4 := by
  set v := ∫ ω, Y ω ^ 2 ∂μ with hvdef
  set q := ∫ ω, Y ω ^ 4 ∂μ with hqdef
  have hm := hY.aestronglyMeasurable (μ := μ)
  have i1 : Integrable Y μ := by simpa using clt_int_of_pow4 hm h4 (k := 1) (by norm_num)
  have i2 : Integrable (fun ω => Y ω ^ 2) μ := clt_int_of_pow4 hm h4 (by norm_num)
  have hv : 0 ≤ v := integral_nonneg fun ω => by positivity
  have hvq : v ^ 2 ≤ q := by
    have h := integral_nonneg (μ := μ) (f := fun ω => (Y ω ^ 2 - v) ^ 2) (fun ω => sq_nonneg _)
    have e : ∫ ω, (Y ω ^ 2 - v) ^ 2 ∂μ = q - 2 * v * v + v ^ 2 := by
      have : (fun ω => (Y ω ^ 2 - v) ^ 2) = fun ω => (Y ω ^ 4 - 2 * v * Y ω ^ 2) + v ^ 2 := by
        funext ω; ring
      have j2 : Integrable (fun ω => 2 * v * Y ω ^ 2) μ := i2.const_mul _
      have j1 : Integrable (fun ω => Y ω ^ 4 - 2 * v * Y ω ^ 2) μ := h4.sub j2
      rw [this, integral_add j1 (integrable_const _), integral_sub h4 j2, integral_const_mul]
      simp
      rfl
    rw [e] at h; nlinarith
  -- polynomial part
  set P : Ω → ℂ := fun ω => (((1 - Y ω ^ 2 / 2 : ℝ)) : ℂ) + ((Y ω : ℝ) : ℂ) * I with hP
  have iA : Integrable (fun ω => (1 - Y ω ^ 2 / 2 : ℝ)) μ :=
    (integrable_const 1).sub (i2.div_const 2)
  have jA : Integrable (fun ω => (((1 - Y ω ^ 2 / 2 : ℝ)) : ℂ)) μ := iA.ofReal
  have jB : Integrable (fun ω => ((Y ω : ℝ) : ℂ) * I) μ := (i1.ofReal (𝕜 := ℂ)).mul_const I
  have iP : Integrable P μ := jA.add jB
  have hPint : ∫ ω, P ω ∂μ = (((1 - v / 2 : ℝ)) : ℂ) := by
    show ∫ ω, ((((1 - Y ω ^ 2 / 2 : ℝ)) : ℂ) + ((Y ω : ℝ) : ℂ) * I) ∂μ = _
    rw [integral_add jA jB, integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal, h0, integral_sub (integrable_const 1) (i2.div_const 2), integral_div]
    simp
    rfl
  have iE : Integrable (fun ω => exp ((Y ω : ℂ) * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall
      fun ω => ?_)
    rw [norm_exp_ofReal_mul_I]
  have ig : Integrable (fun ω => 4 * (δ * Y ω ^ 2 + Y ω ^ 4 / δ)) μ :=
    ((i2.const_mul δ).add (h4.div_const δ)).const_mul 4
  have hT : ‖∫ ω, (exp ((Y ω : ℂ) * I) - P ω) ∂μ‖ ≤ 4 * (δ * v + q / δ) := by
    have := norm_integral_le_of_norm_le (f := fun ω => exp ((Y ω : ℂ) * I) - P ω) ig (Filter.Eventually.of_forall fun ω => by
      have h1 := clt_taylor3 (Y ω)
      have h2 := clt_cube_le (Y ω) hδ
      have e : P ω = 1 + (Y ω : ℂ) * I - (Y ω : ℂ) ^ 2 / 2 := by
        rw [hP]; push_cast; ring
      rw [e]
      calc _ ≤ 4 * |Y ω| ^ 3 := h1
        _ ≤ 4 * (δ * Y ω ^ 2 + Y ω ^ 4 / δ) := by linarith)
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (i2.const_mul δ) (h4.div_const δ), integral_const_mul,
      integral_div]
  have hR : ‖(((1 - v / 2 : ℝ)) : ℂ) - exp (-(v : ℂ) / 2)‖ ≤ q / 4 := by
    have e : exp (-(v : ℂ) / 2) = ((Real.exp (-(v / 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have := clt_exp_neg_bound (w := v / 2) (by positivity)
    calc _ ≤ (v / 2) ^ 2 := this
      _ ≤ q / 4 := by nlinarith
  have hsplit : ∫ ω, exp ((Y ω : ℂ) * I) ∂μ - exp (-(v : ℂ) / 2)
      = ∫ ω, (exp ((Y ω : ℂ) * I) - P ω) ∂μ
        + ((((1 - v / 2 : ℝ)) : ℂ) - exp (-(v : ℂ) / 2)) := by
    rw [integral_sub iE iP, hPint]; ring
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hT hR)

end Census
end IIT
