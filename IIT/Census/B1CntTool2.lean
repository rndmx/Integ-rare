/-
Census, B1 count, WP1 (generic toolkit, no IIT), part 2: the one-dimensional Gaussian comparison
(W5 Lemma GC, W13-effect G4), built from `Lindeberg.lean` in dimension `d = 1`.

* `gaussCDF_lip`: `|Φ(a) - Φ(b)| ≤ |a - b|/√(2π)`;
* `gc_core`: for every smoothing width `ε > 0`,
  `|P(S ≤ x σ) - Φ(x)| ≤ ε/√(2π) + gcErr n ε`, `S = Σ_{l<n} (U_l - 1/2)`, `σ = √(n/12)`,
  `gcErr n ε = n (Kψ/ε)³/6 (E|X|³ + E|G|³)` (Lindeberg; the covariances match exactly);
* `gc_proved : GCStmt` with `ε = n^{-1/8}`, `C = 1 + gcD`.

The summand laws: `gcNu n` = law of `(U - 1/2)/σ` (as a vector of `Fin 1 → ℝ`), and
`gg_sumLaw gcA n` = law of `Z/√n` (GaussGen), whose `n`-fold sum is `gg_law gcA` = `N(0,1)`.
-/
import IIT.Census.B1CntTool1
import IIT.Census.GaussGen
import IIT.Census.Lindeberg

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

/-! ### The standard Gaussian CDF is Lipschitz -/

lemma std_pdf_le (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 / Real.sqrt (2 * Real.pi) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero, one_div]
  have h0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  refine mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 ?_)
  have := sq_nonneg x
  linarith

lemma gauss_Ioc_real_le {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Ioc a b) ≤ (b - a) / Real.sqrt (2 * Real.pi) := by
  have hnn : 0 ≤ ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x :=
    setIntegral_nonneg measurableSet_Ioc fun x _ => gaussianPDFReal_nonneg 0 1 x
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal hnn]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc a b)
    (f := gaussianPDFReal 0 1) (C := 1 / Real.sqrt (2 * Real.pi)) measure_Ioc_lt_top
    (fun x _ => by rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]; exact std_pdf_le x)
  rw [Real.norm_of_nonneg hnn] at h
  have hv : volume.real (Set.Ioc a b) = b - a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  rw [hv] at h
  calc _ ≤ 1 / Real.sqrt (2 * Real.pi) * (b - a) := h
    _ = _ := by ring

lemma gauss_Iic_split {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Iic b) =
      (gaussianReal 0 1).real (Set.Iic a) + (gaussianReal 0 1).real (Set.Ioc a b) := by
  rw [← Set.Iic_union_Ioc_eq_Iic hab, measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]

/-- **The standard Gaussian CDF is `1/√(2π)`-Lipschitz.** -/
theorem gaussCDF_lip (a b : ℝ) :
    |(ProbabilityTheory.gaussianReal 0 1 (Set.Iic a)).toReal -
      (ProbabilityTheory.gaussianReal 0 1 (Set.Iic b)).toReal| ≤ |a - b| / Real.sqrt (2 * Real.pi) := by
  rw [← measureReal_def, ← measureReal_def]
  rcases le_total a b with hab | hab
  · rw [gauss_Iic_split hab, show ∀ p q : ℝ, p - (p + q) = -q from fun p q => by ring, abs_neg,
      abs_of_nonneg measureReal_nonneg, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
    exact gauss_Ioc_real_le hab
  · rw [gauss_Iic_split hab, add_sub_cancel_left, abs_of_nonneg measureReal_nonneg,
      abs_of_nonneg (sub_nonneg.2 hab)]
    exact gauss_Ioc_real_le hab

/-! ### The Gaussian side in dimension one -/

/-- The `1 × 1` coefficient matrix: `gg_law gcA = N(0,1)` on `Fin 1 → ℝ`. -/
def gcA : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

lemma gcA_cov (j k : Fin 1) : gg_cov gcA j k = 1 := by simp [gg_cov, gcA]

lemma gg_law_gcA_orth (a : ℝ) :
    (gg_law gcA).real {x : Fin 1 → ℝ | ∀ j, x j ≤ a} = (gaussianReal 0 1).real (Set.Iic a) := by
  have hmeas : Measurable (fun x : Fin 1 → ℝ => ∑ p, (fun _ => (1 : ℝ)) p * x p) := by fun_prop
  have hset : {x : Fin 1 → ℝ | ∀ j, x j ≤ a} =
      (fun x : Fin 1 → ℝ => ∑ p, (fun _ => (1 : ℝ)) p * x p) ⁻¹' Set.Iic a := by
    ext x; simp [Fin.forall_fin_one]
  rw [hset, ← map_measureReal_apply hmeas measurableSet_Iic, gg_law_functional]
  have : gg_quad (gg_cov gcA) (fun _ => 1) = 1 := by simp [gg_quad, gg_cov, gcA]
  rw [this]; simp

/-- The third absolute moment of `N(0,1)` (as a constant). -/
def gcM3 : ℝ := ∫ x, (∑ p, |x p|) ^ 3 ∂(gg_law gcA)

lemma gcM3_nonneg : 0 ≤ gcM3 := integral_nonneg fun x => by positivity

/-! ### The uniform side in dimension one -/

/-- `σ_n = √(n/12)`. -/
def gcSig (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) / 12)

lemma gcSig_pos {n : ℕ} (hn : 0 < n) : 0 < gcSig n := Real.sqrt_pos.2 (by positivity)

lemma gcSig_sq (n : ℕ) : gcSig n ^ 2 = n / 12 := Real.sq_sqrt (by positivity)

/-- One summand `(u - 1/2)/σ_n` as a vector of `Fin 1 → ℝ`. -/
def gcMap (n : ℕ) (u : ℝ) : Fin 1 → ℝ := fun _ => (u - 1 / 2) / gcSig n

lemma continuous_gcMap (n : ℕ) : Continuous (gcMap n) := by unfold gcMap; fun_prop

lemma measurable_gcMap (n : ℕ) : Measurable (gcMap n) := (continuous_gcMap n).measurable

/-- The law of one normalised summand. -/
def gcNu (n : ℕ) : Measure (Fin 1 → ℝ) := unif.map (gcMap n)

instance (n : ℕ) : IsProbabilityMeasure (gcNu n) := by unfold gcNu; infer_instance

lemma gcNu_integral (n : ℕ) {f : (Fin 1 → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂(gcNu n) = ∫ u, f (gcMap n u) ∂unif :=
  integral_map (measurable_gcMap n).aemeasurable hf.aestronglyMeasurable

lemma gcNu_coord (n : ℕ) (j : Fin 1) : ∫ x, x j ∂(gcNu n) = 0 := by
  rw [gcNu_integral n (measurable_pi_apply j), unif_integral_eq]
  simp only [gcMap]
  rw [intervalIntegral.integral_div, sb_int_lin, zero_div]

lemma gcNu_mul (n : ℕ) (hn : 0 < n) (j k : Fin 1) : ∫ x, x j * x k ∂(gcNu n) = 1 / n := by
  rw [gcNu_integral n (by fun_prop : Measurable fun x : Fin 1 → ℝ => x j * x k), unif_integral_eq]
  have e : ∀ u : ℝ, gcMap n u j * gcMap n u k = (u - 1 / 2) ^ 2 / gcSig n ^ 2 := by
    intro u; simp only [gcMap]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, sb_int_sq, gcSig_sq]
  have : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

lemma gcNu_cube_int (n : ℕ) : Integrable (fun x : Fin 1 → ℝ => (∑ j, |x j|) ^ 3) (gcNu n) := by
  rw [gcNu, integrable_map_measure
    (by fun_prop : Continuous fun x : Fin 1 → ℝ => (∑ j, |x j|) ^ 3).aestronglyMeasurable
    (measurable_gcMap n).aemeasurable]
  exact unif_integrable_of_continuous
    ((by fun_prop : Continuous fun x : Fin 1 → ℝ => (∑ j, |x j|) ^ 3).comp (continuous_gcMap n))

lemma gcNu_cube (n : ℕ) : ∫ x, (∑ j, |x j|) ^ 3 ∂(gcNu n) = (1 / 32) / gcSig n ^ 3 := by
  rw [gcNu_integral n (by fun_prop : Continuous fun x : Fin 1 → ℝ => (∑ j, |x j|) ^ 3).measurable]
  have e : ∀ u : ℝ, (∑ j : Fin 1, |gcMap n u j|) ^ 3 = |u - 1 / 2| ^ 3 / gcSig n ^ 3 := by
    intro u
    simp only [gcMap, Fin.sum_univ_one, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), gcSig, div_pow]
  simp_rw [e]
  rw [integral_div, unif_abs_cube]

/-- Transport of the uniform summands to `Measure.pi unif`. -/
lemma gc_pi_unif (n : ℕ) {F : (Fin 1 → ℝ) → ℝ} (hF : Measurable F) :
    ∫ x, F (∑ β, x β) ∂(Measure.pi fun _ : Fin n => gcNu n) =
      ∫ u, F (fun _ => (∑ l, (u l - 1 / 2)) / gcSig n) ∂(Measure.pi fun _ : Fin n => unif) := by
  have hpi : (Measure.pi fun _ : Fin n => unif).map (fun u (β : Fin n) => gcMap n (u β)) =
      Measure.pi fun _ : Fin n => gcNu n :=
    Measure.pi_map_pi (fun _ => (measurable_gcMap n).aemeasurable)
  have hm : Measurable (fun u : Fin n → ℝ => fun β => gcMap n (u β)) :=
    Measurable.of_eval fun β => (measurable_gcMap n).comp (measurable_pi_apply β)
  have hS : Measurable (fun x : Fin n → Fin 1 → ℝ => ∑ β, x β) :=
    Finset.measurable_sum _ fun β _ => measurable_pi_apply β
  rw [← hpi, integral_map (f := fun x : Fin n → Fin 1 → ℝ => F (∑ β, x β)) hm.aemeasurable
    (hF.comp hS).aestronglyMeasurable]
  congr 1
  funext u
  congr 1
  funext j
  simp only [gcMap, Finset.sum_apply]
  rw [Finset.sum_div]

/-! ### Lindeberg in dimension one -/

/-- The Lindeberg error with smoothing width `ε`. -/
def gcErr (n : ℕ) (ε : ℝ) : ℝ :=
  n * ((lind_Kpsi / ε) ^ 3 / 6 * ((1 / 32) / gcSig n ^ 3 + gcM3 / Real.sqrt n ^ 3))

lemma gc_mismatch (n : ℕ) (hn : 0 < n) (j k : Fin 1) :
    |∫ x, x j * x k ∂(gcNu n) - ∫ x, x j * x k ∂(gg_sumLaw gcA n)| = 0 := by
  rw [gcNu_mul n hn, gg_sumLaw_mul gcA hn, gcA_cov]; simp

lemma gc_up_cmp {n : ℕ} (hn : 0 < n) (c : Fin 1 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    |∫ x, orthUp c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin n => gcNu n)
      - ∫ x, orthUp c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin n => gg_sumLaw gcA n)| ≤ gcErr n ε := by
  have h := lind_orthUp_pi (gcNu_coord n) (gg_sumLaw_coord gcA n) (gcNu_cube_int n)
    (gg_sumLaw_integrable_cube gcA n) c hε n
  refine h.trans (le_of_eq ?_)
  simp only [gc_mismatch n hn, Finset.sum_const_zero, mul_zero, zero_add, gcNu_cube, gg_sumLaw_cube,
    gcErr, gcM3]

lemma gc_low_cmp {n : ℕ} (hn : 0 < n) (c : Fin 1 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    |∫ x, orthLow c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin n => gcNu n)
      - ∫ x, orthLow c ε (∑ β, x β) ∂(Measure.pi fun _ : Fin n => gg_sumLaw gcA n)| ≤ gcErr n ε := by
  have h := lind_orthLow_pi (gcNu_coord n) (gg_sumLaw_coord gcA n) (gcNu_cube_int n)
    (gg_sumLaw_integrable_cube gcA n) c hε n
  refine h.trans (le_of_eq ?_)
  simp only [gc_mismatch n hn, Finset.sum_const_zero, mul_zero, zero_add, gcNu_cube, gg_sumLaw_cube,
    gcErr, gcM3]

/-- The normalised sum as a vector of `Fin 1 → ℝ`. -/
def gcG (n : ℕ) (u : Fin n → ℝ) : Fin 1 → ℝ := fun _ => (∑ l, (u l - 1 / 2)) / gcSig n

lemma measurable_gcG (n : ℕ) : Measurable (gcG n) := by unfold gcG; fun_prop

lemma gc_set_eq {n : ℕ} (hn : 0 < n) (x : ℝ) :
    {u : Fin n → ℝ | ∑ l, (u l - 1 / 2) ≤ x * Real.sqrt ((n : ℝ) / 12)} =
      {u | ∀ j, gcG n u j ≤ (fun _ : Fin 1 => x) j} := by
  ext u
  simp only [Set.mem_ofPred_eq, gcG, Fin.forall_fin_one]
  rw [div_le_iff₀ (gcSig_pos hn), gcSig]

/-- **Gaussian comparison with smoothing width `ε`.** -/
theorem gc_core {n : ℕ} (hn : 0 < n) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |((Measure.pi fun _ : Fin n => unif)
        {u | ∑ l, (u l - 1 / 2) ≤ x * Real.sqrt ((n : ℝ) / 12)}).toReal
      - (gaussianReal 0 1 (Set.Iic x)).toReal| ≤ ε / Real.sqrt (2 * Real.pi) + gcErr n ε := by
  set μ := Measure.pi fun _ : Fin n => unif with hμ
  set c : Fin 1 → ℝ := fun _ => x with hc
  rw [← measureReal_def, ← measureReal_def, gc_set_eq hn x]
  set P := μ.real {u | ∀ j, gcG n u j ≤ c j} with hP
  have hlip1 := gaussCDF_lip (x + ε) x
  have hlip2 := gaussCDF_lip (x - ε) x
  rw [← measureReal_def, ← measureReal_def, show x + ε - x = ε by ring, abs_of_pos hε] at hlip1
  rw [← measureReal_def, ← measureReal_def, show x - ε - x = -ε by ring, abs_neg, abs_of_pos hε] at hlip2
  -- upper bound
  have hU1 : P ≤ ∫ u, orthUp c ε (gcG n u) ∂μ :=
    lind_real_le_integral_orthUp (measurable_gcG n) c hε
  have hU2 : ∫ u, orthUp c ε (gcG n u) ∂μ =
      ∫ y, orthUp c ε (∑ β, y β) ∂(Measure.pi fun _ : Fin n => gcNu n) :=
    (gc_pi_unif n (measurable_orthUp c ε)).symm
  have hU3 := (abs_sub_le_iff.1 (gc_up_cmp hn c hε)).1
  have hU4 : ∫ y, orthUp c ε (∑ β, y β) ∂(Measure.pi fun _ : Fin n => gg_sumLaw gcA n) =
      ∫ y, orthUp c ε y ∂(gg_law gcA) := gg_integral_sum_pi gcA hn (measurable_orthUp c ε)
  have hU5 : ∫ y, orthUp c ε y ∂(gg_law gcA) ≤
      (gg_law gcA).real {y : Fin 1 → ℝ | ∀ j, y j ≤ x + ε} :=
    lind_integral_orthUp_le (μ := gg_law gcA) (g := id) measurable_id c hε
  rw [gg_law_gcA_orth] at hU5
  -- lower bound
  have hL1 : ∫ u, orthLow c ε (gcG n u) ∂μ ≤ P :=
    lind_integral_orthLow_le (measurable_gcG n) c hε
  have hL2 : ∫ u, orthLow c ε (gcG n u) ∂μ =
      ∫ y, orthLow c ε (∑ β, y β) ∂(Measure.pi fun _ : Fin n => gcNu n) :=
    (gc_pi_unif n (measurable_orthLow c ε)).symm
  have hL3 := (abs_sub_le_iff.1 (gc_low_cmp hn c hε)).2
  have hL4 : ∫ y, orthLow c ε (∑ β, y β) ∂(Measure.pi fun _ : Fin n => gg_sumLaw gcA n) =
      ∫ y, orthLow c ε y ∂(gg_law gcA) := gg_integral_sum_pi gcA hn (measurable_orthLow c ε)
  have hL5 : (gg_law gcA).real {y : Fin 1 → ℝ | ∀ j, y j ≤ x - ε} ≤
      ∫ y, orthLow c ε y ∂(gg_law gcA) :=
    lind_real_le_integral_orthLow (μ := gg_law gcA) (g := id) measurable_id c hε
  rw [gg_law_gcA_orth] at hL5
  rw [abs_sub_le_iff]
  constructor
  · have := (abs_sub_le_iff.1 hlip1).1
    linarith
  · have := (abs_sub_le_iff.1 hlip2).2
    linarith

/-- The constant of GC. -/
def gcD : ℝ := lind_Kpsi ^ 3 / 6 * (Real.sqrt 12 ^ 3 / 32 + gcM3)

lemma gcD_nonneg : 0 ≤ gcD := by
  unfold gcD
  have := lind_Kpsi_pos
  have := gcM3_nonneg
  positivity

lemma gcErr_eq {n : ℕ} (hn : 0 < n) :
    gcErr n ((n : ℝ) ^ (-(1 / 8 : ℝ))) = gcD * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set r := (n : ℝ) ^ ((1 : ℝ) / 8) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hn' _
  have hr8 : r ^ 8 = n := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hn'.le]; norm_num
  have hsq : Real.sqrt n = r ^ 4 := by
    rw [← hr8, show r ^ 8 = (r ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have heps : (n : ℝ) ^ (-(1 / 8 : ℝ)) = r⁻¹ := by rw [Real.rpow_neg hn'.le]
  have hsig : gcSig n = r ^ 4 / Real.sqrt 12 := by
    rw [gcSig, Real.sqrt_div (Nat.cast_nonneg n), hsq]
  have h12 : 0 < Real.sqrt 12 := Real.sqrt_pos.2 (by norm_num)
  rw [heps, gcErr, hsig, hsq, ← hr8]
  unfold gcD
  field_simp

/-- **WP1b: one-dimensional Gaussian comparison** (W5 Lemma GC). -/
theorem gc_proved : GCStmt := by
  refine ⟨1 + gcD, by linarith [gcD_nonneg], fun n hn x => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hε : 0 < (n : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hn' _
  have h := gc_core hn x hε
  rw [gcErr_eq hn] at h
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := Real.one_le_sqrt.2 (by nlinarith [Real.pi_gt_three])
  have hd : (n : ℝ) ^ (-(1 / 8 : ℝ)) / Real.sqrt (2 * Real.pi) ≤ (n : ℝ) ^ (-(1 / 8 : ℝ)) :=
    div_le_self hε.le hs
  refine h.trans ?_
  linarith

end

end Census
end IIT
