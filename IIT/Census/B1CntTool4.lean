/-
Census, B1 count, WP1 (generic toolkit, no IIT), part 4: Mills-ratio bounds for the Gaussian tail
(blueprint `B1-W14-count-lean.md` §6, `MillsStmt`).

For `z > 0`, `φ(z) z/(1+z²) ≤ Q(z) ≤ φ(z)/z`, `Q(z) = N(0,1)(z, ∞)`.
* upper: `Q(z) = ∫_z^∞ φ ≤ ∫_z^∞ (t/z) φ(t) dt = φ(z)/z` (`∫_z^∞ t φ = φ(z)`, improper FTC);
* lower: `F(t) = t φ(t)/(1+t²)` has `F' = φ (1 - 2t² - t⁴)/(1+t²)²`, so
  `F(z) = ∫_z^∞ φ (t⁴ + 2t² - 1)/(1+t²)² ≤ ∫_z^∞ φ = Q(z)`.
-/
import IIT.Census.B1CntTool3

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable section

lemma gpdf_eq (t : ℝ) :
    gaussianPDFReal 0 1 t = Real.exp (-(t ^ 2 / 2)) / Real.sqrt (2 * Real.pi) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [neg_div]
  ring

lemma gpdf_hasDeriv (t : ℝ) :
    HasDerivAt (fun t => gaussianPDFReal 0 1 t) (-t * gaussianPDFReal 0 1 t) t := by
  have e : (fun t => gaussianPDFReal 0 1 t) =
      fun t => Real.exp (-(t ^ 2 / 2)) / Real.sqrt (2 * Real.pi) := funext gpdf_eq
  rw [e, gpdf_eq]
  have h := ((((hasDerivAt_pow 2 t).div_const 2).neg).exp).div_const (Real.sqrt (2 * Real.pi))
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
  ring

lemma continuous_gpdf : Continuous fun t => gaussianPDFReal 0 1 t :=
  continuous_iff_continuousAt.2 fun t => (gpdf_hasDeriv t).continuousAt

lemma gpdf_tendsto : Tendsto (fun t => gaussianPDFReal 0 1 t) atTop (𝓝 0) := by
  have e : (fun t => gaussianPDFReal 0 1 t) =
      fun t => Real.exp (-(t ^ 2 / 2)) / Real.sqrt (2 * Real.pi) := funext gpdf_eq
  rw [e]
  have h1 : Tendsto (fun t : ℝ => -(t ^ 2 / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num))
  have := (Real.tendsto_exp_atBot.comp h1).div_const (Real.sqrt (2 * Real.pi))
  simpa using this

lemma gaussQ_eq (z : ℝ) :
    (gaussianReal 0 1 (Ioi z)).toReal = ∫ t in Ioi z, gaussianPDFReal 0 1 t := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Ioi fun t _ => gaussianPDFReal_nonneg 0 1 t)]

lemma gpdf_integrableOn (z : ℝ) : IntegrableOn (fun t => gaussianPDFReal 0 1 t) (Ioi z) :=
  (integrable_gaussianPDFReal 0 1).integrableOn

lemma mulgpdf_integrableOn (z : ℝ) : IntegrableOn (fun t => t * gaussianPDFReal 0 1 t) (Ioi z) := by
  refine Integrable.integrableOn ?_
  have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).div_const
    (Real.sqrt (2 * Real.pi))
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only [gpdf_eq]
  rw [show -(t ^ 2 / 2) = -(1 / 2) * t ^ 2 by ring]
  ring

/-- `∫_z^∞ t φ(t) dt = φ(z)`. -/
lemma integral_Ioi_mul_gpdf (z : ℝ) :
    ∫ t in Ioi z, t * gaussianPDFReal 0 1 t = gaussianPDFReal 0 1 z := by
  have hd : ∀ x ∈ Ioi z, HasDerivAt (fun t => -gaussianPDFReal 0 1 t)
      (x * gaussianPDFReal 0 1 x) x := by
    intro x _
    exact (gpdf_hasDeriv x).neg.congr_deriv (by ring)
  have hint := mulgpdf_integrableOn z
  have ht : Tendsto (fun t => -gaussianPDFReal 0 1 t) atTop (𝓝 0) := by
    simpa using gpdf_tendsto.neg
  have hc : ContinuousWithinAt (fun t => -gaussianPDFReal 0 1 t) (Ici z) z :=
    (gpdf_hasDeriv z).continuousAt.neg.continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint ht]
  ring

/-- The upper Mills bound `Q(z) ≤ φ(z)/z`. -/
lemma mills_upper {z : ℝ} (hz : 0 < z) :
    (gaussianReal 0 1 (Ioi z)).toReal ≤ gaussianPDFReal 0 1 z / z := by
  rw [gaussQ_eq, ← integral_Ioi_mul_gpdf z, ← integral_div]
  have hint := mulgpdf_integrableOn z
  refine setIntegral_mono_on (gpdf_integrableOn z) (hint.div_const z) measurableSet_Ioi
    fun t ht => ?_
  have h0 := gaussianPDFReal_nonneg 0 1 t
  rw [le_div_iff₀ hz]
  have : z ≤ t := le_of_lt ht
  nlinarith

/-- `F(t) = t φ(t)/(1+t²)`. -/
def millsF (t : ℝ) : ℝ := t * gaussianPDFReal 0 1 t / (1 + t ^ 2)

/-- `F'(t) = φ(t) (1 - 2t² - t⁴)/(1+t²)²`. -/
def millsFd (t : ℝ) : ℝ := gaussianPDFReal 0 1 t * ((1 - 2 * t ^ 2 - t ^ 4) / (1 + t ^ 2) ^ 2)

lemma millsF_hasDeriv (t : ℝ) : HasDerivAt millsF (millsFd t) t := by
  have hk : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    have := (hasDerivAt_pow 2 t).const_add 1
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
  have hk0 : 1 + t ^ 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_id t).mul (gpdf_hasDeriv t)).div hk hk0
  have e : millsF = fun t => id t * gaussianPDFReal 0 1 t / (1 + t ^ 2) := rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, id]
  unfold millsFd
  field_simp
  ring

lemma millsRatio_abs_le (t : ℝ) : |(1 - 2 * t ^ 2 - t ^ 4) / (1 + t ^ 2) ^ 2| ≤ 1 := by
  have hk2 : 0 < (1 + t ^ 2) ^ 2 := by positivity
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hk2]; nlinarith [sq_nonneg t]
  · rw [div_le_iff₀ hk2]; nlinarith [sq_nonneg t, pow_nonneg (sq_nonneg t) 2]

lemma continuous_millsFd : Continuous millsFd := by
  unfold millsFd
  refine continuous_gpdf.mul (Continuous.div (by fun_prop) (by fun_prop) fun t => ?_)
  positivity

lemma millsFd_integrableOn (z : ℝ) : IntegrableOn millsFd (Ioi z) := by
  refine Integrable.mono' (gpdf_integrableOn z) continuous_millsFd.aestronglyMeasurable.restrict
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, millsFd, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
  exact mul_le_of_le_one_right (gaussianPDFReal_nonneg 0 1 t) (millsRatio_abs_le t)

lemma millsF_tendsto : Tendsto millsF atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds gpdf_tendsto ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    unfold millsF
    have := gaussianPDFReal_nonneg 0 1 t
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    unfold millsF
    have h0 := gaussianPDFReal_nonneg 0 1 t
    have hk : 0 < 1 + t ^ 2 := by positivity
    rw [div_le_iff₀ hk]
    nlinarith [sq_nonneg (t - 1)]

/-- The lower Mills bound `φ(z) z/(1+z²) ≤ Q(z)` (any `z`). -/
lemma mills_lower (z : ℝ) : millsF z ≤ (gaussianReal 0 1 (Ioi z)).toReal := by
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (millsF_hasDeriv z).continuousAt.continuousWithinAt (fun x _ => millsF_hasDeriv x)
    (millsFd_integrableOn z) millsF_tendsto
  have hF : millsF z = ∫ t in Ioi z, -millsFd t := by
    rw [integral_neg, hFTC]; ring
  rw [hF, gaussQ_eq]
  refine setIntegral_mono_on (millsFd_integrableOn z).neg (gpdf_integrableOn z) measurableSet_Ioi
    fun t _ => ?_
  have h0 := gaussianPDFReal_nonneg 0 1 t
  have h1 := (abs_le.1 (millsRatio_abs_le t)).1
  unfold millsFd
  nlinarith

/-- **WP1c: Mills-ratio bounds for the Gaussian tail.** -/
theorem mills_proved : MillsStmt := by
  intro z hz
  constructor
  · have h := mills_lower z
    have e : Real.exp (-(z ^ 2 / 2)) / Real.sqrt (2 * Real.pi) * (z / (1 + z ^ 2)) = millsF z := by
      rw [millsF, gpdf_eq]; ring
    rw [e]; exact h
  · have h := mills_upper hz
    rwa [gpdf_eq] at h

end

end Census
end IIT
