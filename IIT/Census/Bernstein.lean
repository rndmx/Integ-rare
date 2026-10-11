/-
Census of complexes: generic concentration inequalities for sums of independent real random
variables.

* `bernstein_upper`, `bernstein_abs`: Bernstein's inequality for centred summands bounded by `M`
  with total second moment at most `V`, in the form `exp (-min (ε²/(4V)) (ε/(2M)))`;
* `bernstein_L`: the corollary at the scale `ε = 16 L max (√V) M`, with bound `2 exp (-6L)`;
* `hoeffding_abs`: the two-sided Hoeffding inequality for summands with values in `[0, c i]`.
-/
import Mathlib.Probability.Moments.SubGaussian

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Real

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- One centred summand bounded by `M`: for `0 ≤ t` with `t M ≤ 1`,
`E exp (t X) ≤ exp (t² E X²)`. -/
lemma mgf_le_exp_sq [IsProbabilityMeasure μ] {X : Ω → ℝ} {M t : ℝ} (hX : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ M) (h0 : μ[X] = 0) (ht : 0 ≤ t) (htM : t * M ≤ 1) :
    mgf X μ t ≤ Real.exp (t ^ 2 * μ[fun ω => X ω ^ 2]) := by
  have iX : Integrable X μ :=
    Integrable.of_bound hX.aestronglyMeasurable M (hb.mono fun ω h => by rwa [Real.norm_eq_abs])
  have iX2 : Integrable (fun ω => X ω ^ 2) μ :=
    Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (M ^ 2)
      (hb.mono fun ω h => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2)
  have iE : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    integrable_exp_mul_of_le t M ht hX (hb.mono fun ω h => (le_abs_self _).trans h)
  have hpt : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 + t * X ω + t ^ 2 * X ω ^ 2 := by
    filter_upwards [hb] with ω h
    have h1 : |t * X ω| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht]
      exact (mul_le_mul_of_nonneg_left h ht).trans htM
    have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h1)).2
    rw [mul_pow] at h2
    linarith
  have hint : Integrable (fun ω => 1 + t * X ω + t ^ 2 * X ω ^ 2) μ :=
    ((integrable_const 1).add (iX.const_mul t)).add (iX2.const_mul (t ^ 2))
  calc mgf X μ t = ∫ ω, Real.exp (t * X ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 + t * X ω + t ^ 2 * X ω ^ 2) ∂μ := integral_mono_ae iE hint hpt
    _ = 1 + t ^ 2 * μ[fun ω => X ω ^ 2] := by
        have e1 : ∫ ω, (1 + t * X ω + t ^ 2 * X ω ^ 2) ∂μ
            = ∫ ω, (1 + t * X ω) ∂μ + ∫ ω, t ^ 2 * X ω ^ 2 ∂μ :=
          integral_add (f := fun ω => 1 + t * X ω) (g := fun ω => t ^ 2 * X ω ^ 2)
            ((integrable_const 1).add (iX.const_mul t)) (iX2.const_mul (t ^ 2))
        have e2 : ∫ ω, (1 + t * X ω) ∂μ = ∫ _ω, (1 : ℝ) ∂μ + ∫ ω, t * X ω ∂μ :=
          integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => t * X ω)
            (integrable_const 1) (iX.const_mul t)
        rw [e1, e2, integral_const, integral_const_mul, integral_const_mul, h0]
        simp
    _ ≤ _ := by linarith [Real.add_one_le_exp (t ^ 2 * μ[fun ω => X ω ^ 2])]

/-- **Bernstein's inequality** (upper tail). Independent centred summands bounded by `M` with
total second moment at most `V`. -/
theorem bernstein_upper {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) {M V ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M) (h0 : ∀ i ∈ s, μ[X i] = 0)
    (hV : ∑ i ∈ s, μ[fun ω => X i ω ^ 2] ≤ V) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * M))) := by
  have := hind.isProbabilityMeasure
  have hV0 : 0 ≤ V :=
    (sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg (X i ω)).trans hV
  set t := min (ε / (2 * V)) (1 / M) with ht_def
  have ht : 0 ≤ t := le_min (by positivity) (by positivity)
  have htM : t * M ≤ 1 := by
    rcases hM.eq_or_lt with h | hM'
    · rw [← h, mul_zero]; exact zero_le_one
    · calc t * M ≤ 1 / M * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM
        _ = 1 := by field_simp
  have hmgf : mgf (∑ i ∈ s, X i) μ t ≤ Real.exp (t ^ 2 * V) := by
    rw [hind.mgf_sum₀ hmeas s]
    calc ∏ i ∈ s, mgf (X i) μ t
        ≤ ∏ i ∈ s, Real.exp (t ^ 2 * μ[fun ω => X i ω ^ 2]) :=
          prod_le_prod (fun _ _ => mgf_nonneg)
            (fun i hi => mgf_le_exp_sq (hmeas i) (hb i hi) (h0 i hi) ht htM)
      _ = Real.exp (t ^ 2 * ∑ i ∈ s, μ[fun ω => X i ω ^ 2]) := by
          rw [mul_sum, Real.exp_sum]
      _ ≤ Real.exp (t ^ 2 * V) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hV (sq_nonneg t))
  have hint : Integrable (fun ω => Real.exp (t * (∑ i ∈ s, X i) ω)) μ := by
    refine integrable_exp_mul_of_le t (s.card • M) ht
      (Finset.aemeasurable_sum s fun i _ => hmeas i) ?_
    filter_upwards [(Filter.eventually_all_finset s).2 hb] with ω h
    rw [Finset.sum_apply]
    exact sum_le_card_nsmul s _ M fun i hi => (le_abs_self _).trans (h i hi)
  have hch := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) ε ht hint
  simp only [Finset.sum_apply] at hch
  refine hch.trans ((mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le).trans ?_)
  rw [← Real.exp_add, Real.exp_le_exp]
  have htV : t * V ≤ ε / 2 := by
    rcases hV0.eq_or_lt with h | hVp
    · rw [← h, mul_zero]; positivity
    · calc t * V ≤ ε / (2 * V) * V := mul_le_mul_of_nonneg_right (min_le_left _ _) hV0
        _ = ε / 2 := by field_simp
  have h1 : -t * ε + t ^ 2 * V ≤ -(ε / 2 * t) := by
    have : t * (t * V) ≤ t * (ε / 2) := mul_le_mul_of_nonneg_left htV ht
    nlinarith
  have h2 : ε / 2 * t = min (ε ^ 2 / (4 * V)) (ε / (2 * M)) := by
    rw [ht_def, mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ ε / 2)]
    congr 1 <;> ring
  linarith

/-- **Bernstein's inequality**, two-sided. -/
theorem bernstein_abs {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) {M V ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M) (h0 : ∀ i ∈ s, μ[X i] = 0)
    (hV : ∑ i ∈ s, μ[fun ω => X i ω ^ 2] ≤ V) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|} ≤ 2 * Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * M))) := by
  have := hind.isProbabilityMeasure
  have hup := bernstein_upper s hind hmeas hM hε hb h0 hV
  have hind' : iIndepFun (fun i ω => -X i ω) μ :=
    hind.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hlow := bernstein_upper (X := fun i ω => -X i ω) s hind' (fun i => (hmeas i).neg) hM hε
    (fun i hi => (hb i hi).mono fun ω h => by rwa [abs_neg])
    (fun i hi => by rw [integral_neg, h0 i hi, neg_zero])
    (by simpa only [neg_sq] using hV)
  have hsub : {ω | ε ≤ |∑ i ∈ s, X i ω|} ⊆
      {ω | ε ≤ ∑ i ∈ s, X i ω} ∪ {ω | ε ≤ ∑ i ∈ s, -X i ω} := by
    intro ω hω
    rcases le_abs.mp (show ε ≤ |_| from hω) with h | h
    · exact Or.inl h
    · right
      show ε ≤ ∑ i ∈ s, -X i ω
      rw [Finset.sum_neg_distrib]; exact h
  calc μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|}
      ≤ μ.real ({ω | ε ≤ ∑ i ∈ s, X i ω} ∪ {ω | ε ≤ ∑ i ∈ s, -X i ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} + μ.real {ω | ε ≤ ∑ i ∈ s, -X i ω} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- **Bernstein's inequality** at the scale `ε = 16 L max (√V) M`: for `L ≥ 1` the two-sided
tail is at most `2 exp (-6L)`. -/
theorem bernstein_L {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) {M V L : ℝ} (hL : 1 ≤ L)
    (hpos : 0 < max (Real.sqrt V) M)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M) (h0 : ∀ i ∈ s, μ[X i] = 0)
    (hV : ∑ i ∈ s, μ[fun ω => X i ω ^ 2] ≤ V) :
    μ.real {ω | 16 * L * max (Real.sqrt V) M ≤ |∑ i ∈ s, X i ω|} ≤ 2 * Real.exp (-6 * L) := by
  set mm := max (Real.sqrt V) M with hmm
  have hVm : V ≤ mm ^ 2 := by
    rcases le_total 0 V with h | h
    · calc V = Real.sqrt V ^ 2 := (Real.sq_sqrt h).symm
        _ ≤ mm ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2
    · exact h.trans (sq_nonneg _)
  have hb' : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ mm :=
    fun i hi => (hb i hi).mono fun ω h => h.trans (le_max_right _ _)
  have hε : 0 ≤ 16 * L * mm := by positivity
  have h := bernstein_abs s hind hmeas hpos.le hε hb' h0 (hV.trans hVm)
  refine h.trans ?_
  have hmm0 : mm ≠ 0 := hpos.ne'
  have e1 : (16 * L * mm) ^ 2 / (4 * mm ^ 2) = 64 * L ^ 2 := by field_simp; ring
  have e2 : 16 * L * mm / (2 * mm) = 8 * L := by field_simp; ring
  rw [e1, e2]
  have : 6 * L ≤ min (64 * L ^ 2) (8 * L) := le_min (by nlinarith) (by linarith)
  have := Real.exp_le_exp.mpr (show -min (64 * L ^ 2) (8 * L) ≤ -6 * L by linarith)
  linarith

/-- Centring preserves independence. -/
lemma iIndepFun_sub_const {X : ι → Ω → ℝ} (hind : iIndepFun X μ) (a : ι → ℝ) :
    iIndepFun (fun i ω => X i ω - a i) μ :=
  hind.comp (fun i x => x - a i) (fun i => measurable_sub_const (a i))

/-- **Hoeffding's inequality**, two-sided, for independent summands with values in `[0, c i]`. -/
theorem hoeffding_abs {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) {c : ι → ℝ}
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 (c i)) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, (X i ω - μ[X i])|} ≤
      2 * Real.exp (-2 * ε ^ 2 / ∑ i ∈ s, c i ^ 2) := by
  have := hind.isProbabilityMeasure
  set Y : ι → Ω → ℝ := fun i ω => X i ω - μ[X i] with hY
  have hindY : iIndepFun Y μ := iIndepFun_sub_const hind (fun i => μ[X i])
  have hindY' : iIndepFun (fun i ω => -Y i ω) μ :=
    hindY.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hsubG : ∀ i ∈ s, HasSubgaussianMGF (Y i) ((‖c i - 0‖₊ / 2) ^ 2) μ :=
    fun i hi => hasSubgaussianMGF_of_mem_Icc (hmeas i) (hb i hi)
  have hsubG' : ∀ i ∈ s, HasSubgaussianMGF (fun ω => -Y i ω) ((‖c i - 0‖₊ / 2) ^ 2) μ :=
    fun i hi => (hsubG i hi).neg
  have hup := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindY hsubG hε
  have hlow := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindY' hsubG' hε
  have hc : ((∑ i ∈ s, (‖c i - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) = (∑ i ∈ s, c i ^ 2) / 4 := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_zero, Real.norm_eq_abs, div_pow, sq_abs]
    norm_num
  have hexp : -ε ^ 2 / (2 * ((∑ i ∈ s, (‖c i - 0‖₊ / 2) ^ 2 : NNReal) : ℝ)) =
      -2 * ε ^ 2 / ∑ i ∈ s, c i ^ 2 := by
    rw [hc, show 2 * ((∑ i ∈ s, c i ^ 2) / 4) = (∑ i ∈ s, c i ^ 2) / 2 by ring,
      div_div_eq_mul_div]
    ring
  rw [hexp] at hup hlow
  have hsub : {ω | ε ≤ |∑ i ∈ s, (X i ω - μ[X i])|} ⊆
      {ω | ε ≤ ∑ i ∈ s, Y i ω} ∪ {ω | ε ≤ ∑ i ∈ s, -Y i ω} := by
    intro ω hω
    rcases le_abs.mp (show ε ≤ |_| from hω) with h | h
    · exact Or.inl h
    · right
      show ε ≤ ∑ i ∈ s, -Y i ω
      rw [Finset.sum_neg_distrib]; exact h
  calc μ.real {ω | ε ≤ |∑ i ∈ s, (X i ω - μ[X i])|}
      ≤ μ.real ({ω | ε ≤ ∑ i ∈ s, Y i ω} ∪ {ω | ε ≤ ∑ i ∈ s, -Y i ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ ∑ i ∈ s, Y i ω} + μ.real {ω | ε ≤ ∑ i ∈ s, -Y i ω} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith

end Census
end IIT
