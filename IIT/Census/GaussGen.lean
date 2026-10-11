/-
Census of complexes: explicit Gaussian fields for a `k`-set of units.

Generic part: for a coefficient matrix `A : Fin d → ι → ℝ` the law `gg_law A` of `x = A Z`, `Z` a
standard normal vector indexed by the finite type `ι`.  It is proved that
* the law depends only on the covariance `gg_cov A = A Aᵀ` (`gg_law_eq_of_cov`), and is invariant
  under coordinate permutations preserving the covariance (`gg_law_map_perm`);
* Gaussian stability: `B` iid copies of `A Z / √B` sum to `A Z` in law (`gg_sum_pi_map`), with
  zero means, second moments `C / B` and finite third absolute moments for the summand law;
* the half-space tail `P(h ≤ ⟨v, x⟩) ≤ exp(-h² / (2 vᵀ C v))` (`gg_law_halfspace_le`);
* the small-ball lower bound around any `x = C u` (`gg_law_ball_ge`), with cost `⟨u, x⟩`.

The field of a `k`-set: coordinates `p = t + 2^k i` (unit `i`, pattern `t`),
`ξ_i(t) = √c₀ Z₀ + √c₁ Z_t + √c₂ Z_{i,t}`, law `gg_G k`, covariance
`C_k[p,q] = c₀ + c₁ [t = u] + c₂ [p = q]` (`gg_integral_G_mul`), with the four properties above and
invariance under unit and pattern relabelling (`gg_G_map_relabel`, `gg_G_map_unitPerm`,
`gg_G_map_xor`).

The joint field of two `k`-sets sharing `m` units (`gg_GJ`): an explicit representation through
independent normals, its covariance (`gg_integral_GJ_mul`), marginals equal to `gg_G k`, and the
half-space tail.
-/
import IIT.Census.GaussBox

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Complex

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ### Linear images of standard normal vectors indexed by a finite type -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The standard normal distribution on `ι → ℝ`. -/
def gg_std (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi fun _ => gaussianReal 0 1

instance gg_std_prob (ι : Type*) [Fintype ι] : IsProbabilityMeasure (gg_std ι) := by
  unfold gg_std; infer_instance

/-- The linear map `Z ↦ A Z`. -/
def gg_T (A : Fin d → ι → ℝ) : (ι → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z p => ∑ j, A p j * Z j
      map_add' := fun Z Z' => by
        funext p; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c Z => by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }

lemma gg_T_apply (A : Fin d → ι → ℝ) (Z : ι → ℝ) (p : Fin d) :
    gg_T A Z p = ∑ j, A p j * Z j := rfl

lemma gg_T_single (A : Fin d → ι → ℝ) (j : ι) : gg_T A (Pi.single j 1) = fun p => A p j := by
  funext p
  rw [gg_T_apply]
  simp [Pi.single_apply]

/-- The law of `A Z`. -/
def gg_law (A : Fin d → ι → ℝ) : Measure (Fin d → ℝ) := (gg_std ι).map (gg_T A)

instance gg_law_prob (A : Fin d → ι → ℝ) : IsProbabilityMeasure (gg_law A) := by
  unfold gg_law; infer_instance

/-- The covariance `A Aᵀ`. -/
def gg_cov (A : Fin d → ι → ℝ) (p q : Fin d) : ℝ := ∑ j, A p j * A q j

/-- The quadratic form `vᵀ C v`. -/
def gg_quad (C : Fin d → Fin d → ℝ) (v : Fin d → ℝ) : ℝ := ∑ p, ∑ q, v p * v q * C p q

lemma gg_sum_sq_eq_quad (A : Fin d → ι → ℝ) (v : Fin d → ℝ) :
    ∑ j, (∑ p, v p * A p j) ^ 2 = gg_quad (gg_cov A) v := by
  have e : ∀ j, (∑ p, v p * A p j) ^ 2 = ∑ p, ∑ q, v p * A p j * (v q * A q j) := fun j => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [gg_cov, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma gg_quad_nonneg (A : Fin d → ι → ℝ) (v : Fin d → ℝ) : 0 ≤ gg_quad (gg_cov A) v := by
  rw [← gg_sum_sq_eq_quad]; positivity

lemma gg_charFunDual_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (T : (ι → ℝ) →L[ℝ] F) (L : StrongDual ℝ F) :
    charFunDual ((gg_std ι).map T) L
      = cexp (((-(∑ j, (L (T (Pi.single j 1))) ^ 2) / 2 : ℝ)) : ℂ) := by
  rw [charFunDual_map, gg_std, charFunDual_pi]
  simp_rw [gbox_charFunDual_std1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [neg_div]

lemma gg_dual_apply (L : StrongDual ℝ (Fin d → ℝ)) (x : Fin d → ℝ) :
    L x = ∑ p, x p * L (Pi.single p 1) := by
  rw [gbox_clm_apply L x]
  simp [smul_eq_mul]

lemma gg_sum_sq_dual (A : Fin d → ι → ℝ) (L : StrongDual ℝ (Fin d → ℝ)) :
    ∑ j, (L (gg_T A (Pi.single j 1))) ^ 2 = gg_quad (gg_cov A) fun p => L (Pi.single p 1) := by
  rw [← gg_sum_sq_eq_quad]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gg_T_single, gg_dual_apply]
  simp only [mul_comm]

/-- The law of `A Z` depends only on the covariance `A Aᵀ`. -/
theorem gg_law_eq_of_cov {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (A : Fin d → ι → ℝ)
    (A' : Fin d → ι' → ℝ) (h : ∀ p q, gg_cov A p q = gg_cov A' p q) :
    gg_law A = gg_law A' := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [gg_law, gg_law, gg_charFunDual_map, gg_charFunDual_map, gg_sum_sq_dual, gg_sum_sq_dual]
  have : gg_cov A = gg_cov A' := funext fun p => funext fun q => h p q
  rw [this]

/-- The coordinate permutation `x ↦ x ∘ π` as a continuous linear map. -/
def gg_permCLM (π : Equiv.Perm (Fin d)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x p => x (π p)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Invariance of the law under a coordinate permutation preserving the covariance. -/
theorem gg_law_map_perm (A : Fin d → ι → ℝ) (π : Equiv.Perm (Fin d))
    (h : ∀ p q, gg_cov A (π p) (π q) = gg_cov A p q) :
    (gg_law A).map (fun x p => x (π p)) = gg_law A := by
  have hm : (fun x : Fin d → ℝ => fun p => x (π p)) = ⇑(gg_permCLM π) := rfl
  rw [gg_law, hm, Measure.map_map (gg_permCLM π).measurable (gg_T A).measurable]
  have e : ⇑(gg_permCLM π) ∘ ⇑(gg_T A) = ⇑(gg_T fun p => A (π p)) := rfl
  rw [e]
  exact gg_law_eq_of_cov _ _ fun p q => h p q

/-! ### Moments -/

lemma gg_memLp_coord (j : ι) (r : ENNReal) (hr : r ≠ ⊤) :
    MemLp (fun Z : ι → ℝ => Z j) r (gg_std ι) :=
  (memLp_id_gaussianReal' r hr).comp_measurePreserving (measurePreserving_eval _ j)

lemma gg_integral_coord (A : Fin d → ι → ℝ) (p : Fin d) : ∫ x, x p ∂(gg_law A) = 0 := by
  rw [gg_law, integral_map (gg_T A).measurable.aemeasurable
    (measurable_pi_apply p).aestronglyMeasurable]
  simp only [gg_T_apply]
  rw [integral_finsetSum _ fun j _ =>
    ((gg_memLp_coord j 1 ENNReal.one_ne_top).integrable le_rfl).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul]
  have h0 : ∫ Z, Z j ∂(gg_std ι) = 0 :=
    (integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := j)
      (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable).trans integral_id_gaussianReal
  rw [h0, mul_zero]

lemma gg_integral_coord_mul (j l : ι) :
    ∫ Z, Z j * Z l ∂(gg_std ι) = if j = l then 1 else 0 := by
  split_ifs with h
  · subst h
    exact (integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := j)
      (f := fun x : ℝ => x * x) (measurable_id.mul measurable_id).aestronglyMeasurable).trans
      gbox_integral_sq_std1
  · have e : (fun Z : ι → ℝ => Z j * Z l)
        = fun Z => ∏ i, (if i = j then Z i else 1) * (if i = l then Z i else 1) := by
      funext Z
      rw [Finset.prod_mul_distrib]
      simp
    rw [e, gg_std, integral_fintype_prod_eq_prod
      (f := fun i (x : ℝ) => (if i = j then x else 1) * (if i = l then x else 1))]
    refine Finset.prod_eq_zero (mem_univ j) ?_
    simp [h, integral_id_gaussianReal]

/-- The covariance of `A Z` is `A Aᵀ`. -/
theorem gg_integral_mul (A : Fin d → ι → ℝ) (p q : Fin d) :
    ∫ x, x p * x q ∂(gg_law A) = gg_cov A p q := by
  rw [gg_law, integral_map (f := fun x : Fin d → ℝ => x p * x q) (gg_T A).measurable.aemeasurable
    ((measurable_pi_apply p).mul (measurable_pi_apply q)).aestronglyMeasurable]
  simp only [gg_T_apply, Finset.sum_mul_sum]
  have hint : ∀ j l : ι, Integrable (fun Z : ι → ℝ => A p j * Z j * (A q l * Z l)) (gg_std ι) := by
    intro j l
    have h2 := (gg_memLp_coord j 2 (by simp)).integrable_mul (gg_memLp_coord l 2 (by simp))
    refine (h2.const_mul (A p j * A q l)).congr (ae_of_all _ fun Z => ?_)
    simp only [Pi.mul_apply]
    ring
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hint j l]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => hint j l]
  have e : ∀ l : ι, ∫ Z, A p j * Z j * (A q l * Z l) ∂(gg_std ι)
      = (A p j * A q l) * (if j = l then 1 else 0) := by
    intro l
    rw [← gg_integral_coord_mul j l, ← integral_const_mul]
    congr 1
    funext Z
    ring
  simp_rw [e]
  simp

lemma gg_memLp_T (A : Fin d → ι → ℝ) (p : Fin d) (r : ENNReal) (hr : r ≠ ⊤) :
    MemLp (fun Z => gg_T A Z p) r (gg_std ι) := by
  simp only [gg_T_apply]
  exact memLp_finsetSum _ fun j _ => (gg_memLp_coord j r hr).const_mul _

lemma gg_integrable_cube (A : Fin d → ι → ℝ) :
    Integrable (fun x : Fin d → ℝ => (∑ p, |x p|) ^ 3) (gg_law A) := by
  have hmeas : Measurable (fun x : Fin d → ℝ => (∑ p, |x p|) ^ 3) := by fun_prop
  rw [gg_law, integrable_map_measure hmeas.aestronglyMeasurable (gg_T A).measurable.aemeasurable]
  have hM : MemLp (fun Z => ∑ p, |gg_T A Z p|) ((3 : ℕ) : ENNReal) (gg_std ι) :=
    memLp_finsetSum _ fun p _ => (gg_memLp_T A p _ (by simp)).abs
  refine hM.integrable_norm_pow'.congr (ae_of_all _ fun Z => ?_)
  simp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun p _ => abs_nonneg _)]

/-! ### Stability -/

/-- The law of one of `B` scaled summands `A Z / √B`. -/
def gg_sumLaw (A : Fin d → ι → ℝ) (B : ℕ) : Measure (Fin d → ℝ) :=
  gg_law fun p j => (Real.sqrt B)⁻¹ * A p j

instance gg_sumLaw_prob (A : Fin d → ι → ℝ) (B : ℕ) : IsProbabilityMeasure (gg_sumLaw A B) := by
  unfold gg_sumLaw; infer_instance

lemma gg_sumLaw_coord (A : Fin d → ι → ℝ) (B : ℕ) (p : Fin d) :
    ∫ x, x p ∂(gg_sumLaw A B) = 0 := gg_integral_coord _ p

/-- Second moments of the scaled summand law: `C / B`. -/
lemma gg_sumLaw_mul (A : Fin d → ι → ℝ) {B : ℕ} (hB : 0 < B) (p q : Fin d) :
    ∫ x, x p * x q ∂(gg_sumLaw A B) = gg_cov A p q / B := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : (Real.sqrt B)⁻¹ * (Real.sqrt B)⁻¹ = 1 / B := by
    rw [← mul_inv, Real.mul_self_sqrt hB'.le, one_div]
  rw [gg_sumLaw, gg_integral_mul, gg_cov, gg_cov, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc (Real.sqrt B)⁻¹ * A p j * ((Real.sqrt B)⁻¹ * A q j)
      = ((Real.sqrt B)⁻¹ * (Real.sqrt B)⁻¹) * (A p j * A q j) := by ring
    _ = _ := by rw [hs]; ring

lemma gg_sumLaw_integrable_cube (A : Fin d → ι → ℝ) (B : ℕ) :
    Integrable (fun x : Fin d → ℝ => (∑ p, |x p|) ^ 3) (gg_sumLaw A B) :=
  gg_integrable_cube _

/-- Third absolute moments of the scaled summand law: `C₃ / B^{3/2}`. -/
lemma gg_sumLaw_cube (A : Fin d → ι → ℝ) (B : ℕ) :
    ∫ x, (∑ p, |x p|) ^ 3 ∂(gg_sumLaw A B)
      = (∫ x, (∑ p, |x p|) ^ 3 ∂(gg_law A)) / Real.sqrt B ^ 3 := by
  have hmeas : Measurable (fun x : Fin d → ℝ => (∑ p, |x p|) ^ 3) := by fun_prop
  rw [gg_sumLaw, gg_law, gg_law, integral_map (μ := gg_std ι)
    (gg_T fun p j => (Real.sqrt B)⁻¹ * A p j).measurable.aemeasurable
    hmeas.aestronglyMeasurable, integral_map (μ := gg_std ι) (gg_T A).measurable.aemeasurable
    hmeas.aestronglyMeasurable, ← integral_div]
  congr 1
  funext Z
  have e : ∀ p, gg_T (fun p j => (Real.sqrt B)⁻¹ * A p j) Z p = (Real.sqrt B)⁻¹ * gg_T A Z p := by
    intro p
    simp only [gg_T_apply, Finset.mul_sum, mul_assoc]
  simp only [e, abs_mul, ← Finset.mul_sum, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    inv_pow]
  ring

/-- Gaussian stability: the sum of `B` independent copies of `A Z / √B` has the law of `A Z`. -/
theorem gg_sum_pi_map (A : Fin d → ι → ℝ) {B : ℕ} (hB : 0 < B) :
    (Measure.pi fun _ : Fin B => gg_sumLaw A B).map (fun x => ∑ β, x β) = gg_law A := by
  have hS : (fun x : Fin B → Fin d → ℝ => ∑ β, x β) = ⇑(gbox_sumCLM B d) := by
    funext x; rw [gbox_sumCLM_apply]
  rw [hS]
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_map, charFunDual_pi, gg_law, gg_charFunDual_map]
  have h1 : ∀ β, (L.comp (gbox_sumCLM B d)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin B => Fin d → ℝ) β) = L := by
    intro β
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, gbox_sumCLM_apply, ContinuousLinearMap.single_apply]
    congr 1
    rw [Finset.sum_pi_single']
    simp
  simp_rw [h1]
  simp only [gg_sumLaw, gg_law, gg_charFunDual_map, Finset.prod_const, card_univ, Fintype.card_fin]
  rw [← Complex.exp_nat_mul, ← ofReal_natCast, ← ofReal_mul]
  congr 2
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have e : ∀ j, gg_T (fun p j => (Real.sqrt B)⁻¹ * A p j) (Pi.single j 1)
      = (Real.sqrt B)⁻¹ • gg_T A (Pi.single j 1) := by
    intro j
    rw [gg_T_single, gg_T_single]
    rfl
  simp only [e, map_smul, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow, Real.sq_sqrt hB'.le]
  field_simp

/-- Integral form of Gaussian stability, for measurable test functions. -/
theorem gg_integral_sum_pi (A : Fin d → ι → ℝ) {B : ℕ} (hB : 0 < B) {f : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ x, f (∑ β, x β) ∂(Measure.pi fun _ : Fin B => gg_sumLaw A B) = ∫ x, f x ∂(gg_law A) := by
  have hS : Measurable (fun x : Fin B → Fin d → ℝ => ∑ β, x β) := by
    rw [show (fun x : Fin B → Fin d → ℝ => ∑ β, x β) = ⇑(gbox_sumCLM B d) from
      funext fun x => (gbox_sumCLM_apply B d x).symm]
    exact (gbox_sumCLM B d).measurable
  rw [← integral_map hS.aemeasurable hf.aestronglyMeasurable, gg_sum_pi_map A hB]

/-! ### Half-space tails -/

lemma gg_gauss_tail {V : ℝ} (hV : 0 ≤ V) {h : ℝ} (hh : 0 < h) :
    (gaussianReal 0 V.toNNReal).real {x | h ≤ x} ≤ Real.exp (-h ^ 2 / (2 * V)) := by
  rcases hV.eq_or_lt with hV0 | hVpos
  · subst hV0
    simp only [mul_zero, div_zero, Real.exp_zero]
    exact measureReal_le_one
  · have hc := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 V.toNNReal) (X := id) h
      (t := h / V) (by positivity) (integrable_exp_mul_gaussianReal _)
    rw [mgf_id_gaussianReal, Real.coe_toNNReal _ hV, ← Real.exp_add] at hc
    refine hc.trans_eq (congrArg Real.exp ?_)
    field_simp
    ring

/-- The linear functional `⟨v, x⟩` of `A Z` is a centred real Gaussian of variance `vᵀ C v`. -/
lemma gg_law_functional (A : Fin d → ι → ℝ) (v : Fin d → ℝ) :
    (gg_law A).map (fun x => ∑ p, v p * x p)
      = gaussianReal 0 (gg_quad (gg_cov A) v).toNNReal := by
  set ℓ : (Fin d → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ p, v p * x p
      map_add' := fun x y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring } with hℓ
  have hm : (fun x : Fin d → ℝ => ∑ p, v p * x p) = ⇑ℓ := rfl
  rw [gg_law, hm, Measure.map_map ℓ.measurable (gg_T A).measurable]
  have e : ⇑ℓ ∘ ⇑(gg_T A) = ⇑(ℓ.comp (gg_T A)) := rfl
  rw [e]
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [gg_charFunDual_map, charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  have hL : ∀ x : ℝ, L x = x * L 1 := fun x => by simpa using L.map_smul x 1
  have key : ∑ j, (L ((ℓ.comp (gg_T A)) (Pi.single j 1))) ^ 2
      = (L 1) ^ 2 * gg_quad (gg_cov A) v := by
    rw [← gg_sum_sq_eq_quad, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hL]
    simp only [ContinuousLinearMap.comp_apply, gg_T_single]
    show ((∑ p, v p * A p j) * L 1) ^ 2 = _
    ring
  rw [key, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _),
    Real.coe_toNNReal _ (gg_quad_nonneg A v), map_zero]
  push_cast
  ring_nf

/-- Half-space tail: `P(h ≤ ⟨v, x⟩) ≤ exp(-h² / (2 vᵀ C v))` for `h > 0`. -/
theorem gg_law_halfspace_le (A : Fin d → ι → ℝ) (v : Fin d → ℝ) {h : ℝ} (hh : 0 < h) :
    (gg_law A).real {x | h ≤ ∑ p, v p * x p}
      ≤ Real.exp (-h ^ 2 / (2 * gg_quad (gg_cov A) v)) := by
  have hmeas : Measurable (fun x : Fin d → ℝ => ∑ p, v p * x p) := by fun_prop
  have hset : {x : Fin d → ℝ | h ≤ ∑ p, v p * x p}
      = (fun x : Fin d → ℝ => ∑ p, v p * x p) ⁻¹' Set.Ici h := rfl
  rw [hset, ← map_measureReal_apply hmeas measurableSet_Ici, gg_law_functional]
  exact gg_gauss_tail (gg_quad_nonneg A v) hh

/-! ### Small-ball lower bounds -/

lemma gg_std_box_ge (a : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (2 * ρ / Real.sqrt (2 * Real.pi)) ^ Fintype.card ι
        * Real.exp (-(∑ j, (|a j| + ρ) ^ 2) / 2)
      ≤ (gg_std ι).real (Set.univ.pi fun j => Set.Icc (a j - ρ) (a j + ρ)) := by
  have e : (gg_std ι).real (Set.univ.pi fun j => Set.Icc (a j - ρ) (a j + ρ))
      = ∏ j, (gaussianReal 0 1).real (Set.Icc (a j - ρ) (a j + ρ)) := by
    simp only [measureReal_def, gg_std, Measure.pi_pi, ENNReal.toReal_prod]
  have e2 : (2 * ρ / Real.sqrt (2 * Real.pi)) ^ Fintype.card ι
        * Real.exp (-(∑ j, (|a j| + ρ) ^ 2) / 2)
      = ∏ j, ((a j + ρ) - (a j - ρ))
          * (Real.exp (-((|a j| + ρ) ^ 2) / 2) / Real.sqrt (2 * Real.pi)) := by
    rw [Finset.prod_mul_distrib, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib,
      Real.exp_sum, Finset.prod_div_distrib]
    have : ∀ j, (a j + ρ) - (a j - ρ) = 2 * ρ := fun j => by ring
    simp only [this, Finset.prod_const, card_univ, div_pow, neg_div]
    ring
  rw [e, e2]
  refine Finset.prod_le_prod (fun j _ => by
      have : 0 ≤ (a j + ρ) - (a j - ρ) := by linarith
      positivity) fun j _ => gbox_gauss_Icc_ge _ _ _ (by linarith) fun x hx => ?_
  have h1 : |x| ≤ |a j| + ρ := by
    rw [abs_le]; constructor <;> cases abs_le.1 (le_refl |a j|) <;>
      [linarith [hx.1, neg_abs_le (a j)]; linarith [hx.2, le_abs_self (a j)]]
  have h0 : 0 ≤ |x| := abs_nonneg x
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ (|a j| + ρ) ^ 2 := pow_le_pow_left₀ h0 h1 2

lemma gg_sum_abs_add_sq_le (a : ι → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ j, (|a j| + ρ) ^ 2
      ≤ (Real.sqrt (∑ j, a j ^ 2) + ρ * Real.sqrt (Fintype.card ι)) ^ 2 := by
  have hcs : (∑ j, |a j|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ j, a j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun j => |a j|)
    simpa [sq_abs, card_univ] using this
  have hS : 0 ≤ ∑ j, a j ^ 2 := by positivity
  have hn : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have hsum : ∑ j, |a j| ≤ Real.sqrt (∑ j, a j ^ 2) * Real.sqrt (Fintype.card ι) := by
    rw [← Real.sqrt_mul hS, ← Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg (a j))]
    exact Real.sqrt_le_sqrt (by linarith)
  have e : ∑ j, (|a j| + ρ) ^ 2 = ∑ j, a j ^ 2 + 2 * ρ * ∑ j, |a j| + Fintype.card ι * ρ ^ 2 := by
    simp only [add_sq, sq_abs, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
      card_univ, nsmul_eq_mul]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, add_sq, mul_pow, Real.sq_sqrt hS, Real.sq_sqrt hn]
  nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * ρ)]

/-- Small-ball lower bound around any point `x = C u` of the range of the covariance: the sup-norm
ball of radius `ρ R` (with `R` a bound on the row sums `Σ_j |A p j|`) has probability at least
`(2ρ/√(2π))^{|ι|} exp(-(√⟨u, x⟩ + ρ √|ι|)² / 2)`. -/
theorem gg_law_ball_ge (A : Fin d → ι → ℝ) (u x : Fin d → ℝ)
    (hux : ∀ p, ∑ q, gg_cov A p q * u q = x p) {ρ R : ℝ} (hρ : 0 < ρ)
    (hR : ∀ p, ∑ j, |A p j| ≤ R) :
    (2 * ρ / Real.sqrt (2 * Real.pi)) ^ Fintype.card ι
        * Real.exp (-(Real.sqrt (∑ p, u p * x p) + ρ * Real.sqrt (Fintype.card ι)) ^ 2 / 2)
      ≤ (gg_law A).real {y | ∀ p, |y p - x p| ≤ ρ * R} := by
  set a : ι → ℝ := fun j => ∑ p, A p j * u p with ha
  have hTa : ∀ p, gg_T A a p = x p := by
    intro p
    rw [← hux p, gg_T_apply]
    simp only [ha, gg_cov, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => by ring
  have hcost : ∑ j, a j ^ 2 = ∑ p, u p * x p := by
    have := gg_sum_sq_eq_quad A u
    simp only [ha]
    rw [show (∑ j, (∑ p, A p j * u p) ^ 2) = ∑ j, (∑ p, u p * A p j) ^ 2 by
      simp only [mul_comm], this, gg_quad]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hux p, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hmeasB : MeasurableSet {y : Fin d → ℝ | ∀ p, |y p - x p| ≤ ρ * R} := by
    have : {y : Fin d → ℝ | ∀ p, |y p - x p| ≤ ρ * R}
        = ⋂ p, (fun y : Fin d → ℝ => |y p - x p|) ⁻¹' Set.Iic (ρ * R) := by
      ext y; simp
    rw [this]
    exact MeasurableSet.iInter fun p => (by fun_prop : Measurable _) measurableSet_Iic
  rw [gg_law, map_measureReal_apply (gg_T A).measurable hmeasB]
  refine le_trans ?_ (measureReal_mono (s₁ := Set.univ.pi fun j => Set.Icc (a j - ρ) (a j + ρ)) ?_)
  · refine le_trans ?_ (gg_std_box_ge a hρ)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := gg_sum_abs_add_sq_le a hρ.le
    rw [hcost] at this
    linarith
  · intro Z hZ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    intro p
    rw [← hTa p, gg_T_apply, gg_T_apply, ← Finset.sum_sub_distrib]
    calc |∑ j, (A p j * Z j - A p j * a j)| ≤ ∑ j, |A p j * Z j - A p j * a j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A p j| * ρ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj := hZ j (Set.mem_univ j)
          rw [← mul_sub, abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_le]; constructor <;> linarith [hj.1, hj.2]
      _ = ρ * ∑ j, |A p j| := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ ρ * R := mul_le_mul_of_nonneg_left (hR p) hρ.le

end Generic

/-! ### The field of a `k`-set -/

section KSet

variable (k : ℕ)

/-- The common coefficient `c₀ = 1/4 + 2^{-k}/4`. -/
def gg_c0 : ℝ := 1 / 4 + ((2 : ℝ) ^ k)⁻¹ / 4

/-- The pattern coefficient `c₁ = 2^{-k}/16`. -/
def gg_c1 : ℝ := ((2 : ℝ) ^ k)⁻¹ / 16

/-- The individual coefficient `c₂ = 1/12 - (11/240) 2^{-k}`. -/
def gg_c2 : ℝ := 1 / 12 - 11 / 240 * ((2 : ℝ) ^ k)⁻¹

lemma gg_inv_pow_le : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

lemma gg_c0_pos : 0 < gg_c0 k := by unfold gg_c0; positivity

lemma gg_c1_pos : 0 < gg_c1 k := by unfold gg_c1; positivity

lemma gg_c2_pos : 0 < gg_c2 k := by unfold gg_c2; have := gg_inv_pow_le k; linarith

/-- The unit of the coordinate `p = t + 2^k i`. -/
def gg_unit (p : Fin (k * 2 ^ k)) : Fin k := (finProdFinEquiv.symm p).1

/-- The pattern of the coordinate `p = t + 2^k i`. -/
def gg_pat (p : Fin (k * 2 ^ k)) : Fin (2 ^ k) := (finProdFinEquiv.symm p).2

lemma gg_unit_val (p : Fin (k * 2 ^ k)) : (gg_unit k p : ℕ) = p / 2 ^ k := by
  simp [gg_unit, finProdFinEquiv_symm_apply]

lemma gg_pat_val (p : Fin (k * 2 ^ k)) : (gg_pat k p : ℕ) = p % 2 ^ k := by
  simp [gg_pat, finProdFinEquiv_symm_apply]

/-- The independent inputs: `Z₀`, the pattern inputs `Z_t`, the individual inputs `Z_{i,t}`. -/
abbrev gg_ι := Unit ⊕ Fin (2 ^ k) ⊕ Fin (k * 2 ^ k)

lemma gg_card_ι : Fintype.card (gg_ι k) = 1 + 2 ^ k + k * 2 ^ k := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_fin]
  ring

/-- The coefficients of `ξ_i(t) = √c₀ Z₀ + √c₁ Z_t + √c₂ Z_{i,t}`. -/
def gg_A (p : Fin (k * 2 ^ k)) : gg_ι k → ℝ
  | Sum.inl _ => Real.sqrt (gg_c0 k)
  | Sum.inr (Sum.inl t) => if t = gg_pat k p then Real.sqrt (gg_c1 k) else 0
  | Sum.inr (Sum.inr q) => if q = p then Real.sqrt (gg_c2 k) else 0

/-- The covariance `C_k[p,q] = c₀ + c₁ [t = u] + c₂ [p = q]`. -/
def gg_C (p q : Fin (k * 2 ^ k)) : ℝ :=
  gg_c0 k + gg_c1 k * (if gg_pat k p = gg_pat k q then 1 else 0) + gg_c2 k * (if p = q then 1 else 0)

lemma gg_cov_A (p q : Fin (k * 2 ^ k)) : gg_cov (gg_A k) p q = gg_C k p q := by
  rw [gg_cov, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [gg_A, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const, card_univ, Fintype.card_unit, one_smul,
    Real.mul_self_sqrt (gg_c0_pos k).le, Real.mul_self_sqrt (gg_c1_pos k).le,
    Real.mul_self_sqrt (gg_c2_pos k).le, gg_C]
  simp only [eq_comm (a := gg_pat k q), eq_comm (a := q), mul_one]
  ring

/-- The law `G_k` of the field of a `k`-set. -/
def gg_G : Measure (Fin (k * 2 ^ k) → ℝ) := gg_law (gg_A k)

instance gg_G_prob : IsProbabilityMeasure (gg_G k) := by unfold gg_G; infer_instance

lemma gg_G_coord (p : Fin (k * 2 ^ k)) : ∫ x, x p ∂(gg_G k) = 0 := gg_integral_coord _ p

/-- The covariance of `G_k` is `C_k`. -/
theorem gg_integral_G_mul (p q : Fin (k * 2 ^ k)) : ∫ x, x p * x q ∂(gg_G k) = gg_C k p q := by
  rw [gg_G, gg_integral_mul, gg_cov_A]

lemma gg_G_integrable_cube :
    Integrable (fun x : Fin (k * 2 ^ k) → ℝ => (∑ p, |x p|) ^ 3) (gg_G k) :=
  gg_integrable_cube _

/-- The law of one of `B` scaled summands of `G_k`. -/
def gg_GsumLaw (B : ℕ) : Measure (Fin (k * 2 ^ k) → ℝ) := gg_sumLaw (gg_A k) B

instance gg_GsumLaw_prob (B : ℕ) : IsProbabilityMeasure (gg_GsumLaw k B) := by
  unfold gg_GsumLaw; infer_instance

lemma gg_GsumLaw_coord (B : ℕ) (p : Fin (k * 2 ^ k)) : ∫ x, x p ∂(gg_GsumLaw k B) = 0 :=
  gg_sumLaw_coord _ B p

lemma gg_GsumLaw_mul {B : ℕ} (hB : 0 < B) (p q : Fin (k * 2 ^ k)) :
    ∫ x, x p * x q ∂(gg_GsumLaw k B) = gg_C k p q / B := by
  rw [gg_GsumLaw, gg_sumLaw_mul _ hB, gg_cov_A]

lemma gg_GsumLaw_integrable_cube (B : ℕ) :
    Integrable (fun x : Fin (k * 2 ^ k) → ℝ => (∑ p, |x p|) ^ 3) (gg_GsumLaw k B) :=
  gg_sumLaw_integrable_cube _ B

lemma gg_GsumLaw_cube (B : ℕ) :
    ∫ x, (∑ p, |x p|) ^ 3 ∂(gg_GsumLaw k B)
      = (∫ x, (∑ p, |x p|) ^ 3 ∂(gg_G k)) / Real.sqrt B ^ 3 :=
  gg_sumLaw_cube _ B

/-- Gaussian stability for `G_k`. -/
theorem gg_G_sum_pi_map {B : ℕ} (hB : 0 < B) :
    (Measure.pi fun _ : Fin B => gg_GsumLaw k B).map (fun x => ∑ β, x β) = gg_G k :=
  gg_sum_pi_map _ hB

theorem gg_G_integral_sum_pi {B : ℕ} (hB : 0 < B) {f : (Fin (k * 2 ^ k) → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ x, f (∑ β, x β) ∂(Measure.pi fun _ : Fin B => gg_GsumLaw k B) = ∫ x, f x ∂(gg_G k) :=
  gg_integral_sum_pi _ hB hf

/-- Half-space tail for `G_k`: `P(h ≤ ⟨v, ξ⟩) ≤ exp(-h² / (2 vᵀ C_k v))`. -/
theorem gg_G_halfspace_le (v : Fin (k * 2 ^ k) → ℝ) {h : ℝ} (hh : 0 < h) :
    (gg_G k).real {x | h ≤ ∑ p, v p * x p} ≤ Real.exp (-h ^ 2 / (2 * gg_quad (gg_C k) v)) := by
  have e : gg_C k = gg_cov (gg_A k) := funext fun p => funext fun q => (gg_cov_A k p q).symm
  rw [e]
  exact gg_law_halfspace_le _ v hh

lemma gg_A_row (p : Fin (k * 2 ^ k)) :
    ∑ j, |gg_A k p j| = Real.sqrt (gg_c0 k) + Real.sqrt (gg_c1 k) + Real.sqrt (gg_c2 k) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [gg_A, apply_ite abs, abs_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, card_univ, Fintype.card_unit, one_smul, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Small-ball lower bound for `G_k` around `x = C_k u`, in the sup norm, radius
`ρ (√c₀ + √c₁ + √c₂)`; the cost is `⟨u, x⟩ = xᵀ C_k⁻¹ x`. -/
theorem gg_G_ball_ge (u x : Fin (k * 2 ^ k) → ℝ) (hux : ∀ p, ∑ q, gg_C k p q * u q = x p)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (2 * ρ / Real.sqrt (2 * Real.pi)) ^ (1 + 2 ^ k + k * 2 ^ k)
        * Real.exp (-(Real.sqrt (∑ p, u p * x p)
          + ρ * Real.sqrt ((1 + 2 ^ k + k * 2 ^ k : ℕ) : ℝ)) ^ 2 / 2)
      ≤ (gg_G k).real {y | ∀ p, |y p - x p|
          ≤ ρ * (Real.sqrt (gg_c0 k) + Real.sqrt (gg_c1 k) + Real.sqrt (gg_c2 k))} := by
  rw [← gg_card_ι]
  exact gg_law_ball_ge (gg_A k) u x (fun p => by simp only [gg_cov_A]; exact hux p) hρ
    fun p => (gg_A_row k p).le

/-! ### Relabelling units and patterns -/

/-- The coordinate relabelling `(i, t) ↦ (τ i, ψ t)`. -/
def gg_relabel (τ : Equiv.Perm (Fin k)) (ψ : Equiv.Perm (Fin (2 ^ k))) :
    Equiv.Perm (Fin (k * 2 ^ k)) :=
  finProdFinEquiv.symm.trans ((τ.prodCongr ψ).trans finProdFinEquiv)

lemma gg_unit_relabel (τ : Equiv.Perm (Fin k)) (ψ : Equiv.Perm (Fin (2 ^ k))) (p : Fin (k * 2 ^ k)) :
    gg_unit k (gg_relabel k τ ψ p) = τ (gg_unit k p) := by
  simp [gg_unit, gg_relabel]

lemma gg_pat_relabel (τ : Equiv.Perm (Fin k)) (ψ : Equiv.Perm (Fin (2 ^ k))) (p : Fin (k * 2 ^ k)) :
    gg_pat k (gg_relabel k τ ψ p) = ψ (gg_pat k p) := by
  simp [gg_pat, gg_relabel]

/-- `G_k` is invariant under every relabelling `(i, t) ↦ (τ i, ψ t)`. -/
theorem gg_G_map_relabel (τ : Equiv.Perm (Fin k)) (ψ : Equiv.Perm (Fin (2 ^ k))) :
    (gg_G k).map (fun x p => x (gg_relabel k τ ψ p)) = gg_G k := by
  refine gg_law_map_perm _ _ fun p q => ?_
  rw [gg_cov_A, gg_cov_A, gg_C, gg_C, gg_pat_relabel, gg_pat_relabel]
  simp only [ψ.injective.eq_iff, (gg_relabel k τ ψ).injective.eq_iff]

/-- The pattern permutation induced by a unit permutation `σ`: bit `σ q` of the image is bit `q`. -/
def gg_bitPerm (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (2 ^ k)) :=
  (finFunctionFinEquiv.symm.trans (σ.arrowCongr (Equiv.refl (Fin 2)))).trans finFunctionFinEquiv

lemma gg_bitPerm_bit (σ : Equiv.Perm (Fin k)) (t : Fin (2 ^ k)) (q : Fin k) :
    finFunctionFinEquiv.symm (gg_bitPerm k σ t) (σ q) = finFunctionFinEquiv.symm t q := by
  simp [gg_bitPerm, Equiv.arrowCongr_apply]

/-- `G_k` is invariant under unit permutations. -/
theorem gg_G_map_unitPerm (σ : Equiv.Perm (Fin k)) :
    (gg_G k).map (fun x p => x (gg_relabel k σ (gg_bitPerm k σ) p)) = gg_G k :=
  gg_G_map_relabel k σ _

/-- The pattern translation `t ↦ t xor s`. -/
def gg_xor (s : Fin (2 ^ k)) : Equiv.Perm (Fin (2 ^ k)) :=
  Function.Involutive.toPerm (fun t => ⟨t.val ^^^ s.val, Nat.xor_lt_two_pow t.2 s.2⟩)
    fun t => Fin.ext (by simp)

lemma gg_xor_val (s t : Fin (2 ^ k)) : (gg_xor k s t : ℕ) = t.val ^^^ s.val := rfl

/-- `G_k` is invariant under pattern translations. -/
theorem gg_G_map_xor (s : Fin (2 ^ k)) :
    (gg_G k).map (fun x p => x (gg_relabel k (Equiv.refl _) (gg_xor k s) p)) = gg_G k :=
  gg_G_map_relabel k _ _

end KSet

/-! ### Generic reindexing -/

section Reindex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d d' : ℕ}

/-- The coordinate selection `x ↦ x ∘ f` as a continuous linear map. -/
def gg_selCLM (f : Fin d' → Fin d) : (Fin d → ℝ) →L[ℝ] (Fin d' → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x p => x (f p)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Selecting coordinates of `A Z` gives the law of the selected rows of `A`. -/
theorem gg_law_map_sel (A : Fin d → ι → ℝ) (f : Fin d' → Fin d) :
    (gg_law A).map (fun x p => x (f p)) = gg_law fun p => A (f p) := by
  have hm : (fun x : Fin d → ℝ => fun p => x (f p)) = ⇑(gg_selCLM f) := rfl
  rw [gg_law, hm, Measure.map_map (gg_selCLM f).measurable (gg_T A).measurable]
  rfl

end Reindex

/-! ### The joint field of two `k`-sets sharing `m` units

The first set is the units `0, …, k-1` of a union of `2k - m` units, the second the units
`k-m, …, 2k-m-1`; the shared units are `k-m, …, k-1`.  A pattern of the first set has the bits of
its `k - m` own units low and the bits of the shared units high; a pattern of the second set has the
bits of the shared units low and those of its own units high.  A pattern of the union is a triple
`(own₁, shared, own₂)`.  A joint coordinate `P = p + (k 2^k) w` is the coordinate `p` of the set
`w ∈ {0, 1}`. -/

section Joint

variable (k m : ℕ)

lemma gg_pow_le : 2 ^ k ≤ 2 ^ (k - m) * 2 ^ m := by
  rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Own bits of a pattern of the first set. -/
def gg_lo0 (t : Fin (2 ^ k)) : Fin (2 ^ (k - m)) := ⟨t % 2 ^ (k - m), Nat.mod_lt _ (by positivity)⟩

/-- Shared bits of a pattern of the first set. -/
def gg_hi0 (t : Fin (2 ^ k)) : Fin (2 ^ m) :=
  ⟨t / 2 ^ (k - m), by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    exact lt_of_lt_of_le t.2 (by rw [mul_comm]; exact gg_pow_le k m)⟩

/-- Shared bits of a pattern of the second set. -/
def gg_lo1 (t : Fin (2 ^ k)) : Fin (2 ^ m) := ⟨t % 2 ^ m, Nat.mod_lt _ (by positivity)⟩

/-- Own bits of a pattern of the second set. -/
def gg_hi1 (t : Fin (2 ^ k)) : Fin (2 ^ (k - m)) :=
  ⟨t / 2 ^ m, by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    exact lt_of_lt_of_le t.2 (gg_pow_le k m)⟩

lemma gg_lohi0_inj {t u : Fin (2 ^ k)} (h1 : gg_lo0 k m t = gg_lo0 k m u)
    (h2 : gg_hi0 k m t = gg_hi0 k m u) : t = u := by
  simp only [gg_lo0, gg_hi0, Fin.mk.injEq] at h1 h2
  ext
  rw [← Nat.mod_add_div t.val (2 ^ (k - m)), ← Nat.mod_add_div u.val (2 ^ (k - m)), h1, h2]

lemma gg_lohi1_inj {t u : Fin (2 ^ k)} (h1 : gg_lo1 k m t = gg_lo1 k m u)
    (h2 : gg_hi1 k m t = gg_hi1 k m u) : t = u := by
  simp only [gg_lo1, gg_hi1, Fin.mk.injEq] at h1 h2
  ext
  rw [← Nat.mod_add_div t.val (2 ^ m), ← Nat.mod_add_div u.val (2 ^ m), h1, h2]

/-- Patterns of the union: `(own bits of the first set, shared bits, own bits of the second)`. -/
abbrev gg_ρ := Fin (2 ^ (k - m)) × Fin (2 ^ m) × Fin (2 ^ (k - m))


lemma gg_fin2 (w : Fin 2) : w = 0 ∨ w = 1 := by
  rcases w with ⟨_ | _ | n, h⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- The shared bits of the pattern `t` of the set `w`. -/
def gg_shb (w : Fin 2) (t : Fin (2 ^ k)) : Fin (2 ^ m) :=
  if w = 0 then gg_hi0 k m t else gg_lo1 k m t

/-- First factor of the restriction indicator (own bits of the first set). -/
def gg_e1 (w : Fin 2) (t : Fin (2 ^ k)) (x : Fin (2 ^ (k - m))) : ℝ :=
  if w = 0 then (if x = gg_lo0 k m t then 1 else 0) else 1

/-- Second factor of the restriction indicator (shared bits). -/
def gg_e2 (w : Fin 2) (t : Fin (2 ^ k)) (y : Fin (2 ^ m)) : ℝ :=
  if y = gg_shb k m w t then 1 else 0

/-- Third factor of the restriction indicator (own bits of the second set). -/
def gg_e3 (w : Fin 2) (t : Fin (2 ^ k)) (z : Fin (2 ^ (k - m))) : ℝ :=
  if w = 0 then 1 else (if z = gg_hi1 k m t then 1 else 0)

/-- The indicator that the union pattern `ρ` restricts to the pattern `t` of the set `w`. -/
def gg_ind (w : Fin 2) (t : Fin (2 ^ k)) (ρ : gg_ρ k m) : ℝ :=
  gg_e1 k m w t ρ.1 * gg_e2 k m w t ρ.2.1 * gg_e3 k m w t ρ.2.2

lemma gg_sum_dd {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    ∑ x, (if x = a then (1 : ℝ) else 0) * (if x = b then 1 else 0) = if a = b then 1 else 0 := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

lemma gg_sum_d1 {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ x, (if x = a then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq']; simp

lemma gg_sum_ind_mul (w w' : Fin 2) (t u : Fin (2 ^ k)) :
    ∑ ρ, gg_ind k m w t ρ * gg_ind k m w' u ρ
      = if w = w' then (2 : ℝ) ^ (k - m) * (if t = u then 1 else 0)
        else if gg_shb k m w t = gg_shb k m w' u then 1 else 0 := by
  have e : ∑ ρ, gg_ind k m w t ρ * gg_ind k m w' u ρ
      = (∑ x, gg_e1 k m w t x * gg_e1 k m w' u x) * ((∑ y, gg_e2 k m w t y * gg_e2 k m w' u y)
          * (∑ z, gg_e3 k m w t z * gg_e3 k m w' u z)) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [gg_ind]
    ring
  have h2 : ∑ y, gg_e2 k m w t y * gg_e2 k m w' u y
      = if gg_shb k m w t = gg_shb k m w' u then 1 else 0 := gg_sum_dd _ _
  rw [e, h2]
  have hc : ((Finset.univ : Finset (Fin (2 ^ (k - m)))).card : ℝ) = 2 ^ (k - m) := by simp
  rcases gg_fin2 w with rfl | rfl <;> rcases gg_fin2 w' with rfl | rfl
  · simp only [gg_e1, gg_e3, ite_true, mul_one, Finset.sum_const, nsmul_eq_mul, hc, gg_sum_dd,
      gg_shb]
    by_cases htu : t = u
    · subst htu; simp
    · have : ¬ (gg_lo0 k m t = gg_lo0 k m u ∧ gg_hi0 k m t = gg_hi0 k m u) :=
        fun h => htu (gg_lohi0_inj k m h.1 h.2)
      by_cases h1 : gg_lo0 k m t = gg_lo0 k m u
      · simp [htu, h1, show gg_hi0 k m t ≠ gg_hi0 k m u from fun h => this ⟨h1, h⟩]
      · simp [htu, h1]
  · simp only [gg_e1, gg_e3, ite_true, mul_one, one_mul, gg_sum_d1,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, show (0 : Fin 2) ≠ 1 by decide]
  · simp only [gg_e1, gg_e3, ite_true, mul_one, one_mul, gg_sum_d1,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, show (0 : Fin 2) ≠ 1 by decide]
  · simp only [gg_e1, gg_e3, ite_true, mul_one, Finset.sum_const, nsmul_eq_mul, hc,
      gg_sum_dd, gg_shb, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    by_cases htu : t = u
    · subst htu; simp
    · have : ¬ (gg_lo1 k m t = gg_lo1 k m u ∧ gg_hi1 k m t = gg_hi1 k m u) :=
        fun h => htu (gg_lohi1_inj k m h.1 h.2)
      by_cases h1 : gg_lo1 k m t = gg_lo1 k m u
      · simp [htu, h1, show gg_hi1 k m t ≠ gg_hi1 k m u from fun h => this ⟨h1, h⟩]
      · simp [htu, h1]

/-- The set of a joint coordinate. -/
def gg_jw (P : Fin (2 * (k * 2 ^ k))) : Fin 2 := (finProdFinEquiv.symm P).1

/-- The coordinate within its set of a joint coordinate. -/
def gg_jp (P : Fin (2 * (k * 2 ^ k))) : Fin (k * 2 ^ k) := (finProdFinEquiv.symm P).2

/-- The joint coordinate of the coordinate `p` of the set `w`. -/
def gg_jidx (w : Fin 2) (p : Fin (k * 2 ^ k)) : Fin (2 * (k * 2 ^ k)) := finProdFinEquiv (w, p)

@[simp] lemma gg_jw_jidx (w : Fin 2) (p : Fin (k * 2 ^ k)) : gg_jw k (gg_jidx k w p) = w := by
  simp [gg_jw, gg_jidx]

@[simp] lemma gg_jp_jidx (w : Fin 2) (p : Fin (k * 2 ^ k)) : gg_jp k (gg_jidx k w p) = p := by
  simp [gg_jp, gg_jidx]

lemma gg_P_ext {P Q : Fin (2 * (k * 2 ^ k))} (hw : gg_jw k P = gg_jw k Q)
    (hu : gg_unit k (gg_jp k P) = gg_unit k (gg_jp k Q))
    (ht : gg_pat k (gg_jp k P) = gg_pat k (gg_jp k Q)) : P = Q := by
  have hp : gg_jp k P = gg_jp k Q :=
    finProdFinEquiv.symm.injective (Prod.ext hu ht)
  exact finProdFinEquiv.symm.injective (Prod.ext hw hp)

/-- The label of the unit of a joint coordinate in the union `0, …, 2k-m-1`. -/
def gg_glob (P : Fin (2 * (k * 2 ^ k))) : ℕ :=
  (if gg_jw k P = 0 then 0 else k - m) + gg_unit k (gg_jp k P)

/-- A unit label of the union is shared. -/
def gg_shared (g : ℕ) : Prop := k - m ≤ g ∧ g < k

instance (g : ℕ) : Decidable (gg_shared k m g) := by unfold gg_shared; infer_instance

/-- `β = 2^{-(2k-m)}/16`. -/
def gg_beta : ℝ := ((2 : ℝ) ^ (2 * k - m))⁻¹ / 16

/-- `α = 2^{-(2k-m)} (2^m/12 - 11/240)`. -/
def gg_alpha : ℝ := ((2 : ℝ) ^ (2 * k - m))⁻¹ * ((2 : ℝ) ^ m / 12 - 11 / 240)

/-- The residual individual variance of a shared unit, `(1 - 2^{m-k})/12`. -/
def gg_rS : ℝ := (1 - (2 : ℝ) ^ m / (2 : ℝ) ^ k) / 12

/-- The residual individual variance of a joint coordinate. -/
def gg_r2 (P : Fin (2 * (k * 2 ^ k))) : ℝ :=
  if gg_shared k m (gg_glob k m P) then gg_rS k m else gg_c2 k

lemma gg_beta_pos : 0 < gg_beta k m := by unfold gg_beta; positivity

lemma gg_alpha_pos : 0 < gg_alpha k m := by
  unfold gg_alpha
  have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) < 2 ^ m / 12 - 11 / 240 := by linarith
  positivity

lemma gg_rS_nonneg (hm : m ≤ k) : 0 ≤ gg_rS k m := by
  unfold gg_rS
  have h1 : (2 : ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hm
  have h2 : (2 : ℝ) ^ m / 2 ^ k ≤ 1 := (div_le_one (by positivity)).2 h1
  linarith

lemma gg_r2_nonneg (hm : m ≤ k) (P : Fin (2 * (k * 2 ^ k))) : 0 ≤ gg_r2 k m P := by
  unfold gg_r2; split_ifs
  · exact gg_rS_nonneg k m hm
  · exact (gg_c2_pos k).le

lemma gg_pow_split (hm : m ≤ k) : (2 : ℝ) ^ (2 * k - m) = 2 ^ k * 2 ^ (k - m) := by
  rw [← pow_add]; congr 1; omega

lemma gg_beta_mul (hm : m ≤ k) : gg_beta k m * 2 ^ (k - m) = gg_c1 k := by
  rw [gg_beta, gg_c1, gg_pow_split k m hm]
  field_simp

lemma gg_alpha_mul (hm : m ≤ k) : gg_alpha k m * 2 ^ (k - m) + gg_rS k m = gg_c2 k := by
  rw [gg_alpha, gg_rS, gg_c2, gg_pow_split k m hm]
  field_simp
  ring

/-- The independent inputs of the joint field: `Z₀`, one input per pattern of the union, one input
per shared unit and pattern of the union, one individual input per joint coordinate. -/
abbrev gg_ιJ := Unit ⊕ gg_ρ k m ⊕ (Fin m × gg_ρ k m) ⊕ Fin (2 * (k * 2 ^ k))

/-- The coefficients of the joint field
`ξ_P = √c₀ Z₀ + √β Σ_{ρ ↦ t} V_ρ + [shared] √α Σ_{ρ ↦ t} V_{i,ρ} + √r_P R_P`. -/
def gg_AJ (P : Fin (2 * (k * 2 ^ k))) : gg_ιJ k m → ℝ
  | Sum.inl _ => Real.sqrt (gg_c0 k)
  | Sum.inr (Sum.inl ρ) => Real.sqrt (gg_beta k m) * gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
  | Sum.inr (Sum.inr (Sum.inl sρ)) => Real.sqrt (gg_alpha k m)
      * ((if sρ.1.val + (k - m) = gg_glob k m P then 1 else 0)
        * gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) sρ.2)
  | Sum.inr (Sum.inr (Sum.inr Q)) => if Q = P then Real.sqrt (gg_r2 k m P) else 0

lemma gg_sum_s (hm : m ≤ k) (g g' : ℕ) :
    ∑ s : Fin m, (if s.val + (k - m) = g then (1 : ℝ) else 0) * (if s.val + (k - m) = g' then 1 else 0)
      = if g = g' ∧ gg_shared k m g then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, h1, h2⟩ := h
    have e : ∀ s : Fin m, (if s.val + (k - m) = g then (1 : ℝ) else 0)
        * (if s.val + (k - m) = g then 1 else 0)
        = if s = ⟨g - (k - m), by omega⟩ then 1 else 0 := by
      intro s
      by_cases hs : s.val + (k - m) = g
      · rw [ite_eq_left hs, ite_eq_left (Fin.ext (by simp; omega))]; ring
      · rw [ite_eq_right hs, ite_eq_right (fun h' => hs (by rw [h']; simp; omega))]; ring
    simp only [e]
    exact gg_sum_d1 _
  · refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : s.val + (k - m) = g
    · by_cases hs' : s.val + (k - m) = g'
      · exact absurd ⟨hs.symm.trans hs', by constructor <;> omega⟩ h
      · simp [hs']
    · simp [hs]

/-- The joint covariance, as it comes out of the representation. -/
lemma gg_cov_AJ_expand (hm : m ≤ k) (P Q : Fin (2 * (k * 2 ^ k))) :
    gg_cov (gg_AJ k m) P Q
      = gg_c0 k + gg_beta k m * (∑ ρ, gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
            * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) ρ)
        + gg_alpha k m * (if gg_glob k m P = gg_glob k m Q ∧ gg_shared k m (gg_glob k m P) then 1 else 0)
          * (∑ ρ, gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
            * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) ρ)
        + (if P = Q then gg_r2 k m P else 0) := by
  rw [gg_cov, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [gg_AJ]
  have h0 : ∑ _u : Unit, Real.sqrt (gg_c0 k) * Real.sqrt (gg_c0 k) = gg_c0 k := by
    simp [Real.mul_self_sqrt (gg_c0_pos k).le]
  have h1 : ∑ ρ : gg_ρ k m, Real.sqrt (gg_beta k m) * gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
      * (Real.sqrt (gg_beta k m) * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) ρ)
      = gg_beta k m * ∑ ρ, gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
            * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) ρ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    linear_combination (gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
      * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) ρ) * Real.mul_self_sqrt (gg_beta_pos k m).le
  have h2 : ∑ sρ : Fin m × gg_ρ k m, Real.sqrt (gg_alpha k m)
        * ((if sρ.1.val + (k - m) = gg_glob k m P then 1 else 0)
          * gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) sρ.2)
      * (Real.sqrt (gg_alpha k m) * ((if sρ.1.val + (k - m) = gg_glob k m Q then 1 else 0)
          * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) sρ.2))
      = gg_alpha k m * (if gg_glob k m P = gg_glob k m Q ∧ gg_shared k m (gg_glob k m P) then 1 else 0)
          * (∑ ρ, gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
            * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) ρ) := by
    rw [Fintype.sum_prod_type, ← gg_sum_s k m hm, mul_assoc, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun ρ _ => ?_
    linear_combination ((if s.val + (k - m) = gg_glob k m P then (1 : ℝ) else 0)
      * gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) ρ
      * ((if s.val + (k - m) = gg_glob k m Q then (1 : ℝ) else 0)
      * gg_ind k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) ρ)) * Real.mul_self_sqrt (gg_alpha_pos k m).le
  have h3 : ∑ R : Fin (2 * (k * 2 ^ k)), (if R = P then Real.sqrt (gg_r2 k m P) else 0)
      * (if R = Q then Real.sqrt (gg_r2 k m Q) else 0) = if P = Q then gg_r2 k m P else 0 := by
    by_cases h : P = Q
    · subst h
      rw [Finset.sum_eq_single P (fun R _ hR => by simp [hR]) (by simp)]
      simp [Real.mul_self_sqrt (gg_r2_nonneg k m hm P)]
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero fun R _ => ?_
      by_cases hR : R = P
      · subst hR; simp [h]
      · simp [hR]
  rw [h0, h1, h2, h3]
  ring

/-- The joint covariance in closed form: inside a set it is `C_k`; across the two sets it is
`c₀ + (β + α [same unit]) [the shared bits agree]`. -/
def gg_CJ (P Q : Fin (2 * (k * 2 ^ k))) : ℝ :=
  gg_c0 k + if gg_jw k P = gg_jw k Q then
      gg_c1 k * (if gg_pat k (gg_jp k P) = gg_pat k (gg_jp k Q) then 1 else 0)
        + gg_c2 k * (if P = Q then 1 else 0)
    else (gg_beta k m + gg_alpha k m * (if gg_glob k m P = gg_glob k m Q then 1 else 0))
      * (if gg_shb k m (gg_jw k P) (gg_pat k (gg_jp k P))
          = gg_shb k m (gg_jw k Q) (gg_pat k (gg_jp k Q)) then 1 else 0)

theorem gg_cov_AJ (hm : m ≤ k) (P Q : Fin (2 * (k * 2 ^ k))) :
    gg_cov (gg_AJ k m) P Q = gg_CJ k m P Q := by
  rw [gg_cov_AJ_expand k m hm, gg_sum_ind_mul, gg_CJ]
  by_cases hw : gg_jw k P = gg_jw k Q
  · rw [ite_eq_left hw, ite_eq_left hw]
    by_cases hPQ : P = Q
    · subst hPQ
      have := gg_alpha_mul k m hm
      have hb := gg_beta_mul k m hm
      by_cases hs : gg_shared k m (gg_glob k m P)
      · simp only [gg_r2, hs, and_self, ite_true]
        linear_combination hb + this
      · simp only [gg_r2, hs, and_false, ite_false, ite_true]
        linear_combination hb
    · have hb := gg_beta_mul k m hm
      by_cases ht : gg_pat k (gg_jp k P) = gg_pat k (gg_jp k Q)
      · have hg : ¬ gg_glob k m P = gg_glob k m Q := by
          intro hg
          refine hPQ (gg_P_ext k hw (Fin.ext ?_) ht)
          simp only [gg_glob, hw] at hg
          omega
        simp only [ht, hg, hPQ, false_and, ite_true, ite_false]
        linear_combination hb
      · simp only [ht, hPQ, ite_false]
        ring
  · have hPQ : P ≠ Q := fun h => hw (h ▸ rfl)
    rw [ite_eq_right hw, ite_eq_right hw, ite_eq_right hPQ]
    have hg : (gg_glob k m P = gg_glob k m Q ∧ gg_shared k m (gg_glob k m P))
        ↔ gg_glob k m P = gg_glob k m Q := by
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      have hu1 := (gg_unit k (gg_jp k P)).2
      have hu2 := (gg_unit k (gg_jp k Q)).2
      unfold gg_glob at h
      unfold gg_shared gg_glob
      rcases gg_fin2 (gg_jw k P) with h1 | h1 <;> rcases gg_fin2 (gg_jw k Q) with h2 | h2 <;>
        simp only [h1, h2, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h ⊢ <;>
        first | exact absurd (h1.trans h2.symm) hw | omega
    simp only [hg]
    split_ifs <;> ring

/-- The joint law of the fields of two `k`-sets sharing `m` units. -/
def gg_GJ : Measure (Fin (2 * (k * 2 ^ k)) → ℝ) := gg_law (gg_AJ k m)

instance gg_GJ_prob : IsProbabilityMeasure (gg_GJ k m) := by unfold gg_GJ; infer_instance

lemma gg_GJ_coord (P : Fin (2 * (k * 2 ^ k))) : ∫ x, x P ∂(gg_GJ k m) = 0 :=
  gg_integral_coord _ P

/-- The covariance of the joint law. -/
theorem gg_integral_GJ_mul (hm : m ≤ k) (P Q : Fin (2 * (k * 2 ^ k))) :
    ∫ x, x P * x Q ∂(gg_GJ k m) = gg_CJ k m P Q := by
  rw [gg_GJ, gg_integral_mul, gg_cov_AJ k m hm]

lemma gg_CJ_jidx (w : Fin 2) (p q : Fin (k * 2 ^ k)) :
    gg_CJ k m (gg_jidx k w p) (gg_jidx k w q) = gg_C k p q := by
  have hpq : (gg_jidx k w p = gg_jidx k w q) ↔ p = q := by
    constructor
    · intro h; simpa using congrArg (gg_jp k) h
    · rintro rfl; rfl
  simp only [gg_CJ, gg_C, gg_jw_jidx, gg_jp_jidx, ite_true, hpq]
  ring

/-- Each of the two sets of the joint field has the law `G_k`. -/
theorem gg_GJ_marginal (hm : m ≤ k) (w : Fin 2) :
    (gg_GJ k m).map (fun x p => x (gg_jidx k w p)) = gg_G k := by
  rw [gg_GJ, gg_law_map_sel, gg_G]
  refine gg_law_eq_of_cov _ _ fun p q => ?_
  show gg_cov (gg_AJ k m) (gg_jidx k w p) (gg_jidx k w q) = _
  rw [gg_cov_AJ k m hm, gg_CJ_jidx, gg_cov_A]

/-- Half-space tail for the joint law: `P(h ≤ ⟨v, ξ⟩) ≤ exp(-h² / (2 vᵀ C_J v))`. -/
theorem gg_GJ_halfspace_le (hm : m ≤ k) (v : Fin (2 * (k * 2 ^ k)) → ℝ) {h : ℝ} (hh : 0 < h) :
    (gg_GJ k m).real {x | h ≤ ∑ P, v P * x P}
      ≤ Real.exp (-h ^ 2 / (2 * gg_quad (gg_CJ k m) v)) := by
  have e : gg_CJ k m = gg_cov (gg_AJ k m) :=
    funext fun P => funext fun Q => (gg_cov_AJ k m hm P Q).symm
  rw [e]
  exact gg_law_halfspace_le _ v hh

/-- The law of one of `B` scaled summands of the joint law. -/
def gg_GJsumLaw (B : ℕ) : Measure (Fin (2 * (k * 2 ^ k)) → ℝ) := gg_sumLaw (gg_AJ k m) B

instance gg_GJsumLaw_prob (B : ℕ) : IsProbabilityMeasure (gg_GJsumLaw k m B) := by
  unfold gg_GJsumLaw; infer_instance

lemma gg_GJsumLaw_coord (B : ℕ) (P : Fin (2 * (k * 2 ^ k))) :
    ∫ x, x P ∂(gg_GJsumLaw k m B) = 0 := gg_sumLaw_coord _ B P

lemma gg_GJsumLaw_mul (hm : m ≤ k) {B : ℕ} (hB : 0 < B) (P Q : Fin (2 * (k * 2 ^ k))) :
    ∫ x, x P * x Q ∂(gg_GJsumLaw k m B) = gg_CJ k m P Q / B := by
  rw [gg_GJsumLaw, gg_sumLaw_mul _ hB, gg_cov_AJ k m hm]

lemma gg_GJsumLaw_integrable_cube (B : ℕ) :
    Integrable (fun x : Fin (2 * (k * 2 ^ k)) → ℝ => (∑ P, |x P|) ^ 3) (gg_GJsumLaw k m B) :=
  gg_sumLaw_integrable_cube _ B

lemma gg_GJsumLaw_cube (B : ℕ) :
    ∫ x, (∑ P, |x P|) ^ 3 ∂(gg_GJsumLaw k m B)
      = (∫ x, (∑ P, |x P|) ^ 3 ∂(gg_GJ k m)) / Real.sqrt B ^ 3 :=
  gg_sumLaw_cube _ B

/-- Gaussian stability for the joint law. -/
theorem gg_GJ_sum_pi_map {B : ℕ} (hB : 0 < B) :
    (Measure.pi fun _ : Fin B => gg_GJsumLaw k m B).map (fun x => ∑ β, x β) = gg_GJ k m :=
  gg_sum_pi_map _ hB

theorem gg_GJ_integral_sum_pi {B : ℕ} (hB : 0 < B) {f : (Fin (2 * (k * 2 ^ k)) → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ x, f (∑ β, x β) ∂(Measure.pi fun _ : Fin B => gg_GJsumLaw k m B) = ∫ x, f x ∂(gg_GJ k m) :=
  gg_integral_sum_pi _ hB hf

end Joint

end

end Census
end IIT
