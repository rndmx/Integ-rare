/-
Multivariate Lyapunov central limit theorem for triangular arrays (fourth moments), in
portmanteau form for closed sets, used as `clt_lyapunov_closed` in `PairCLT.lean`.  Route: characteristic functions (product over independent summands,
per-summand Taylor estimate from `CLTSummand`), Lévy continuity
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`), portmanteau
(`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`).  Imports only Mathlib.
-/
import IIT.Census.CLTSummand
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Complex Filter Topology Finset

section Vec

variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {Z : Ω → EuclideanSpace ℝ ι}

lemma clt_inner_eq (x u : EuclideanSpace ℝ ι) : inner ℝ x u = ∑ a, x a * u a := by
  simp [PiLp.inner_apply, mul_comm]

lemma clt_int_of_le_sq (h4 : Integrable (fun ω => ‖Z ω‖ ^ 4) μ)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hb : ∀ ω, |f ω| ≤ ‖Z ω‖ ^ 2) :
    Integrable f μ := by
  refine (h4.add (integrable_const (1 : ℝ))).mono' hf (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  refine (hb ω).trans ?_
  have := norm_nonneg (Z ω)
  simp only [Pi.add_apply]; nlinarith [sq_nonneg (‖Z ω‖ ^ 2 - 1)]

lemma clt_int_vec (hZ : Measurable Z) (h4 : Integrable (fun ω => ‖Z ω‖ ^ 4) μ) :
    Integrable Z μ := by
  refine (h4.add (integrable_const (1 : ℝ))).mono' hZ.aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have := norm_nonneg (Z ω)
  simp only [Pi.add_apply]; nlinarith [sq_nonneg (‖Z ω‖ - 1), sq_nonneg (‖Z ω‖ ^ 2 - 1)]

lemma clt_inner_pow4_le (x u : EuclideanSpace ℝ ι) :
    (inner ℝ x u) ^ 4 ≤ ‖u‖ ^ 4 * ‖x‖ ^ 4 := by
  have h := abs_real_inner_le_norm x u
  have e : (inner ℝ x u) ^ 4 = |inner ℝ x u| ^ 4 := by
    rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
  rw [e, ← mul_pow, mul_comm ‖u‖]
  exact pow_le_pow_left₀ (abs_nonneg _) h 4

omit [IsProbabilityMeasure μ] in
lemma clt_int_inner_pow4 (hZ : Measurable Z) (h4 : Integrable (fun ω => ‖Z ω‖ ^ 4) μ)
    (u : EuclideanSpace ℝ ι) : Integrable (fun ω => (inner ℝ (Z ω) u) ^ 4) μ := by
  refine (h4.const_mul (‖u‖ ^ 4)).mono' (by fun_prop : Measurable fun ω => (inner ℝ (Z ω) u) ^ 4).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact clt_inner_pow4_le _ _

lemma clt_integral_inner_zero (hZ : Measurable Z) (h4 : Integrable (fun ω => ‖Z ω‖ ^ 4) μ)
    (h0 : ∫ ω, Z ω ∂μ = 0) (u : EuclideanSpace ℝ ι) : ∫ ω, inner ℝ (Z ω) u ∂μ = 0 := by
  have hc : ∀ ω, inner ℝ (Z ω) u = inner ℝ u (Z ω) := fun ω => real_inner_comm _ _
  simp_rw [hc]
  rw [integral_inner (clt_int_vec hZ h4) u, h0, inner_zero_right]

lemma clt_int_mul (hZ : Measurable Z) (h4 : Integrable (fun ω => ‖Z ω‖ ^ 4) μ) (a b : ι) :
    Integrable (fun ω => Z ω a * Z ω b) μ := by
  refine clt_int_of_le_sq h4 (by fun_prop) fun ω => ?_
  rw [abs_mul, sq]
  have ha := PiLp.norm_apply_le (Z ω) a
  have hb := PiLp.norm_apply_le (Z ω) b
  rw [Real.norm_eq_abs] at ha hb
  exact mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)

lemma clt_integral_sq_inner (hZ : Measurable Z) (h4 : Integrable (fun ω => ‖Z ω‖ ^ 4) μ)
    (u : EuclideanSpace ℝ ι) :
    ∫ ω, (inner ℝ (Z ω) u) ^ 2 ∂μ = ∑ a, ∑ b, u a * u b * ∫ ω, Z ω a * Z ω b ∂μ := by
  have e : ∀ ω, (inner ℝ (Z ω) u) ^ 2 = ∑ a, ∑ b, u a * u b * (Z ω a * Z ω b) := by
    intro ω
    rw [clt_inner_eq, sq, Finset.sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (clt_int_mul hZ h4 a b).const_mul _]
  refine sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (clt_int_mul hZ h4 a b).const_mul _]
  refine sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

end Vec

section Array

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, MeasureTheory.Measure (Ω n)}
    [∀ n, MeasureTheory.IsProbabilityMeasure (P n)] {m : ℕ → ℕ}
    {X : ∀ n, Fin (m n) → Ω n → EuclideanSpace ℝ ι} {C : Matrix ι ι ℝ}

omit [DecidableEq ι] in
lemma clt_V_tendsto (hmeas : ∀ n j, Measurable (X n j))
    (hint : ∀ n j, MeasureTheory.Integrable (fun ω => ‖X n j ω‖ ^ 4) (P n))
    (hcov : ∀ a b : ι, Filter.Tendsto (fun n => ∑ j, ∫ ω, X n j ω a * X n j ω b ∂P n)
      Filter.atTop (nhds (C a b)))
    (u : EuclideanSpace ℝ ι) :
    Tendsto (fun n => ∑ j, ∫ ω, (inner ℝ (X n j ω) u) ^ 2 ∂P n) atTop
      (𝓝 (∑ a, ∑ b, u a * u b * C a b)) := by
  have e : ∀ n, ∑ a, ∑ b, u a * u b * ∑ j, ∫ ω, X n j ω a * X n j ω b ∂P n
      = ∑ j, ∫ ω, (inner ℝ (X n j ω) u) ^ 2 ∂P n := by
    intro n
    simp_rw [clt_integral_sq_inner (hmeas n _) (hint n _), Finset.mul_sum]
    exact (sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  exact (tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
    (hcov a b).const_mul _).congr e

open Matrix in
omit [DecidableEq ι] in
lemma clt_posSemidef (hmeas : ∀ n j, Measurable (X n j))
    (hint : ∀ n j, MeasureTheory.Integrable (fun ω => ‖X n j ω‖ ^ 4) (P n))
    (hcov : ∀ a b : ι, Filter.Tendsto (fun n => ∑ j, ∫ ω, X n j ω a * X n j ω b ∂P n)
      Filter.atTop (nhds (C a b))) : C.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
  · simp only [star_trivial]
    refine tendsto_nhds_unique (hcov j i) ?_
    simpa [mul_comm] using hcov i j
  · have hV := clt_V_tendsto hmeas hint hcov (WithLp.toLp 2 x)
    have e : star x ⬝ᵥ (C *ᵥ x) = ∑ a, ∑ b, (WithLp.toLp 2 x) a * (WithLp.toLp 2 x) b * C a b := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      ring
    rw [e]
    exact ge_of_tendsto' hV fun n => sum_nonneg fun j _ =>
      integral_nonneg fun ω => sq_nonneg _

lemma clt_charFun_gauss (hC : C.PosSemidef) (u : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian 0 C) u = exp (-((∑ a, ∑ b, u a * u b * C a b : ℝ) : ℂ) / 2) := by
  rw [charFun_multivariateGaussian hC u]
  congr 1
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [neg_div]
  congr 2
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

omit [DecidableEq ι] in
lemma clt_charFun_bound (hmeas : ∀ n j, Measurable (X n j))
    (hind : ∀ n, ProbabilityTheory.iIndepFun (X n) (P n))
    (hint : ∀ n j, MeasureTheory.Integrable (fun ω => ‖X n j ω‖ ^ 4) (P n))
    (hmean : ∀ n j, ∫ ω, X n j ω ∂P n = 0) (u : EuclideanSpace ℝ ι) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖charFun ((P n).map (fun ω => ∑ j, X n j ω)) u
        - exp (-((∑ j, ∫ ω, (inner ℝ (X n j ω) u) ^ 2 ∂P n : ℝ) : ℂ) / 2)‖
      ≤ ∑ j, (4 * (δ * ∫ ω, (inner ℝ (X n j ω) u) ^ 2 ∂P n
          + (∫ ω, (inner ℝ (X n j ω) u) ^ 4 ∂P n) / δ)
          + (∫ ω, (inner ℝ (X n j ω) u) ^ 4 ∂P n) / 4) := by
  set v : Fin (m n) → ℝ := fun j => ∫ ω, (inner ℝ (X n j ω) u) ^ 2 ∂P n with hv
  have hprod : charFun ((P n).map (fun ω => ∑ j, X n j ω)) u
      = ∏ j, charFun ((P n).map (X n j)) u := by
    rw [(hind n).charFun_map_fun_sum_eq_prod (fun j => (hmeas n j).aemeasurable),
      Finset.prod_apply]
  have hexp : exp (-((∑ j, v j : ℝ) : ℂ) / 2) = ∏ j, exp (-((v j : ℝ) : ℂ) / 2) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  rw [hprod, hexp]
  refine (clt_norm_prod_sub_prod_le _ _ _ (fun j _ => norm_charFun_le_one _)
    (fun j _ => ?_)).trans (sum_le_sum fun j _ => ?_)
  · rw [Complex.norm_exp, Real.exp_le_one_iff]
    have : 0 ≤ v j := integral_nonneg fun ω => sq_nonneg _
    simp only [neg_re, div_ofNat_re, ofReal_re]
    linarith
  · rw [charFun_apply, integral_map (hmeas n j).aemeasurable (by fun_prop)]
    exact clt_summand (by fun_prop)
      (clt_int_inner_pow4 (hmeas n j) (hint n j) u)
      (clt_integral_inner_zero (hmeas n j) (hint n j) (hmean n j) u) hδ

omit [DecidableEq ι] in
lemma clt_charFun_tendsto (hmeas : ∀ n j, Measurable (X n j))
    (hind : ∀ n, ProbabilityTheory.iIndepFun (X n) (P n))
    (hint : ∀ n j, MeasureTheory.Integrable (fun ω => ‖X n j ω‖ ^ 4) (P n))
    (hmean : ∀ n j, ∫ ω, X n j ω ∂P n = 0)
    (hcov : ∀ a b : ι, Filter.Tendsto (fun n => ∑ j, ∫ ω, X n j ω a * X n j ω b ∂P n)
      Filter.atTop (nhds (C a b)))
    (hlyap : Filter.Tendsto (fun n => ∑ j, ∫ ω, ‖X n j ω‖ ^ 4 ∂P n) Filter.atTop (nhds 0))
    (u : EuclideanSpace ℝ ι) :
    Tendsto (fun n => charFun ((P n).map (fun ω => ∑ j, X n j ω)) u) atTop
      (𝓝 (exp (-((∑ a, ∑ b, u a * u b * C a b : ℝ) : ℂ) / 2))) := by
  set Q := ∑ a, ∑ b, u a * u b * C a b
  set V : ℕ → ℝ := fun n => ∑ j, ∫ ω, (inner ℝ (X n j ω) u) ^ 2 ∂P n with hVdef
  have hV : Tendsto V atTop (𝓝 Q) := clt_V_tendsto hmeas hint hcov u
  set M : ℕ → ℝ := fun n => ‖u‖ ^ 4 * ∑ j, ∫ ω, ‖X n j ω‖ ^ 4 ∂P n with hMdef
  have hM : Tendsto M atTop (𝓝 0) := by simpa using hlyap.const_mul (‖u‖ ^ 4)
  have hM0 : ∀ n, 0 ≤ M n := fun n =>
    mul_nonneg (by positivity) (sum_nonneg fun j _ => integral_nonneg fun ω => by positivity)
  set δ : ℕ → ℝ := fun n => √(M n) + 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have := Real.sqrt_nonneg (M n)
    simp only [hδdef]; linarith
  have hsq : Tendsto (fun n => √(M n)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hM
    rw [Real.sqrt_zero] at h
    exact h
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h := hsq.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact h
  have hbound : ∀ n, ‖charFun ((P n).map (fun ω => ∑ j, X n j ω)) u - exp (-((V n : ℝ) : ℂ) / 2)‖
      ≤ 4 * (δ n * V n + √(M n)) + M n / 4 := by
    intro n
    refine (clt_charFun_bound hmeas hind hint hmean u n (hδpos n)).trans ?_
    set q : Fin (m n) → ℝ := fun j => ∫ ω, (inner ℝ (X n j ω) u) ^ 4 ∂P n with hq
    have hsum : ∑ j, (4 * (δ n * ∫ ω, (inner ℝ (X n j ω) u) ^ 2 ∂P n + q j / δ n) + q j / 4)
        = 4 * (δ n * V n + (∑ j, q j) / δ n) + (∑ j, q j) / 4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_div, ← Finset.sum_div]
    rw [hsum]
    have hQ4 : ∑ j, q j ≤ M n := by
      simp only [hMdef, Finset.mul_sum]
      refine sum_le_sum fun j _ => ?_
      rw [← integral_const_mul]
      exact integral_mono (clt_int_inner_pow4 (hmeas n j) (hint n j) u)
        ((hint n j).const_mul _) fun ω => clt_inner_pow4_le _ _
    have hQ40 : 0 ≤ ∑ j, q j := sum_nonneg fun j _ => integral_nonneg fun ω => by positivity
    have hsM : √(M n) ≤ δ n := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simp only [hδdef]; linarith
    have hdiv : (∑ j, q j) / δ n ≤ √(M n) := by
      rw [div_le_iff₀ (hδpos n)]
      have h1 := Real.mul_self_sqrt (hM0 n)
      have h2 := Real.sqrt_nonneg (M n)
      nlinarith
    have hV0 : 0 ≤ V n := sum_nonneg fun j _ => integral_nonneg fun ω => sq_nonneg _
    nlinarith
  have hβ : Tendsto (fun n => 4 * (δ n * V n + √(M n)) + M n / 4) atTop (𝓝 0) := by
    simpa using (((hδ.mul hV).add hsq).const_mul 4).add (hM.div_const 4)
  have hE : Tendsto (fun n => exp (-((V n : ℝ) : ℂ) / 2)) atTop (𝓝 (exp (-((Q : ℝ) : ℂ) / 2))) :=
    (Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp hV).neg.div_const 2)
  have hD := squeeze_zero_norm hbound hβ
  simpa using hD.add hE

end Array

/-- **Multivariate Lyapunov CLT, portmanteau form** (used as `clt_lyapunov_closed`
in `PairCLT.lean`). -/
theorem clt_lyapunov_closed_thm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, MeasureTheory.Measure (Ω n))
    [∀ n, MeasureTheory.IsProbabilityMeasure (P n)] (m : ℕ → ℕ)
    (X : ∀ n, Fin (m n) → Ω n → EuclideanSpace ℝ ι) (C : Matrix ι ι ℝ)
    (hmeas : ∀ n j, Measurable (X n j)) (hind : ∀ n, ProbabilityTheory.iIndepFun (X n) (P n))
    (hint : ∀ n j, MeasureTheory.Integrable (fun ω => ‖X n j ω‖ ^ 4) (P n))
    (hmean : ∀ n j, ∫ ω, X n j ω ∂P n = 0)
    (hcov : ∀ a b : ι, Filter.Tendsto (fun n => ∑ j, ∫ ω, X n j ω a * X n j ω b ∂P n) Filter.atTop (nhds (C a b)))
    (hlyap : Filter.Tendsto (fun n => ∑ j, ∫ ω, ‖X n j ω‖ ^ 4 ∂P n) Filter.atTop (nhds 0))
    (F : Set (EuclideanSpace ℝ ι)) (hF : IsClosed F) :
    Filter.limsup (fun n => P n {ω | ∑ j, X n j ω ∈ F}) Filter.atTop ≤ ProbabilityTheory.multivariateGaussian 0 C F := by
  have hC := clt_posSemidef hmeas hint hcov
  have hS : ∀ n, Measurable (fun ω => ∑ j, X n j ω) := fun n =>
    Finset.measurable_fun_sum _ fun j _ => hmeas n j
  let μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ ι) := fun n =>
    ⟨(P n).map (fun ω => ∑ j, X n j ω), inferInstance⟩
  let μ0 : ProbabilityMeasure (EuclideanSpace ℝ ι) := ⟨multivariateGaussian 0 C, inferInstance⟩
  have hT : Tendsto μs atTop (𝓝 μ0) := ProbabilityMeasure.tendsto_of_tendsto_charFun fun u => by
    show Tendsto (fun n => charFun ((P n).map (fun ω => ∑ j, X n j ω)) u) atTop
      (𝓝 (charFun (multivariateGaussian 0 C) u))
    rw [clt_charFun_gauss hC u]
    exact clt_charFun_tendsto hmeas hind hint hmean hcov hlyap u
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hT hF
  have e : (fun n => P n {ω | ∑ j, X n j ω ∈ F}) = fun n => (μs n : Measure _) F := by
    funext n
    show _ = (P n).map (fun ω => ∑ j, X n j ω) F
    rw [Measure.map_apply (hS n) hF.measurableSet]
    rfl
  rw [e]
  exact h

end Census
end IIT
