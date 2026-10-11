/-
Census of complexes: the explicit Gaussian side of the tightness argument.

The limit law of the six cause-side differences of a pair is represented through twelve independent
standard normals, `η = T Z` with an explicit linear map `gbox_T6`.  This file proves
* the covariance of `η` (`gbox_integral_G6_mul`), zero means and finite third moments;
* Gaussian stability: `B` independent copies of `T Z / √B` sum to `T Z` in law (`gbox_sum_pi_map`);
* a lower bound on the probability of the negative orthant box (`gbox_G6_box_ge`,
  `gbox_eventually_G6_box`) and an upper bound on the probability of a coordinate slab
  (`gbox_G6_slab_le`);
* the same facts for two independent copies (`gbox_T12`, `gbox_G12_eq`, `gbox_G12_prod`,
  `gbox_G12_orthant`, `gbox_integral_G12_mul`, `gbox_G12_slab_le`).
-/
import IIT.Census.TightStats
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Complex

noncomputable section

/-! ### Standard normal vectors and their linear images -/

/-- The standard normal distribution on `Fin m → ℝ`. -/
def gbox_std (m : ℕ) : Measure (Fin m → ℝ) := Measure.pi fun _ => gaussianReal 0 1

instance gbox_std_prob (m : ℕ) : IsProbabilityMeasure (gbox_std m) := by
  unfold gbox_std; infer_instance

lemma gbox_charFunDual_std1 (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = cexp (((-(L 1) ^ 2 / 2 : ℝ)) : ℂ) := by
  rw [charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap, charFun_gaussianReal]
  congr 1
  simp only [map_zero, ofReal_zero, mul_zero, zero_mul, zero_sub, mul_one,
    Real.coe_toNNReal _ (sq_nonneg _)]
  push_cast
  ring

/-- The characteristic function of a linear image of a standard normal vector. -/
lemma gbox_charFunDual_map {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (T : (Fin m → ℝ) →L[ℝ] F) (L : StrongDual ℝ F) :
    charFunDual ((gbox_std m).map T) L
      = cexp (((-(∑ k, (L (T (Pi.single k 1))) ^ 2) / 2 : ℝ)) : ℂ) := by
  rw [charFunDual_map, gbox_std, charFunDual_pi]
  simp_rw [gbox_charFunDual_std1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [neg_div]

/-- The law of one of `B` scaled summands `T Z / √B`. -/
def gbox_sumLaw {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (B : ℕ) : Measure (Fin d → ℝ) :=
  (gbox_std m).map ⇑((Real.sqrt B)⁻¹ • T)

instance gbox_sumLaw_prob {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (B : ℕ) :
    IsProbabilityMeasure (gbox_sumLaw T B) :=
  by unfold gbox_sumLaw; infer_instance

/-- The summation map as a continuous linear map. -/
def gbox_sumCLM (B d : ℕ) : (Fin B → Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ∑ β : Fin B, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin B => Fin d → ℝ) β

lemma gbox_sumCLM_apply (B d : ℕ) (x : Fin B → Fin d → ℝ) : gbox_sumCLM B d x = ∑ β, x β := by
  simp [gbox_sumCLM]

/-- Gaussian stability: the sum of `B` independent copies of `T Z / √B` has the law of `T Z`. -/
theorem gbox_sum_pi_map {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) {B : ℕ} (hB : 0 < B) :
    (Measure.pi fun _ : Fin B => gbox_sumLaw T B).map (fun x => ∑ β, x β) = (gbox_std m).map T := by
  have hS : (fun x : Fin B → Fin d → ℝ => ∑ β, x β) = ⇑(gbox_sumCLM B d) := by
    funext x; rw [gbox_sumCLM_apply]
  rw [hS]
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_map, charFunDual_pi, gbox_charFunDual_map]
  have h1 : ∀ β, (L.comp (gbox_sumCLM B d)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin B => Fin d → ℝ) β) = L := by
    intro β
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, gbox_sumCLM_apply, ContinuousLinearMap.single_apply]
    congr 1
    rw [Finset.sum_pi_single']
    simp
  simp_rw [h1]
  simp only [gbox_sumLaw, gbox_charFunDual_map, Finset.prod_const, card_univ, Fintype.card_fin]
  rw [← Complex.exp_nat_mul, ← ofReal_natCast, ← ofReal_mul]
  congr 2
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  simp only [smul_apply, map_smul, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    inv_pow, Real.sq_sqrt hB'.le]
  field_simp

/-- Integral form of Gaussian stability, for measurable test functions. -/
theorem gbox_integral_sum_pi {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) {B : ℕ} (hB : 0 < B)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f (∑ β, x β) ∂(Measure.pi fun _ : Fin B => gbox_sumLaw T B)
      = ∫ Z, f (T Z) ∂(gbox_std m) := by
  have hS : Measurable (fun x : Fin B → Fin d → ℝ => ∑ β, x β) := by
    rw [show (fun x : Fin B → Fin d → ℝ => ∑ β, x β) = ⇑(gbox_sumCLM B d) from
      funext fun x => (gbox_sumCLM_apply B d x).symm]
    exact (gbox_sumCLM B d).measurable
  rw [← integral_map hS.aemeasurable hf.aestronglyMeasurable, gbox_sum_pi_map T hB,
    integral_map T.measurable.aemeasurable hf.aestronglyMeasurable]

/-! ### Moments -/

lemma gbox_memLp_coord (m : ℕ) (k : Fin m) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun Z : Fin m → ℝ => Z k) p (gbox_std m) :=
  (memLp_id_gaussianReal' p hp).comp_measurePreserving (measurePreserving_eval _ k)

lemma gbox_integral_coord (m : ℕ) (k : Fin m) : ∫ Z, Z k ∂(gbox_std m) = 0 := by
  exact (integral_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := k)
    (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable).trans integral_id_gaussianReal

lemma gbox_integral_sq_std1 : ∫ x, x * x ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  simpa [sq] using h

lemma gbox_integral_coord_mul (m : ℕ) (k l : Fin m) :
    ∫ Z, Z k * Z l ∂(gbox_std m) = if k = l then 1 else 0 := by
  split_ifs with h
  · subst h
    exact (integral_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := k)
      (f := fun x : ℝ => x * x) (measurable_id.mul measurable_id).aestronglyMeasurable).trans
      gbox_integral_sq_std1
  · have e : (fun Z : Fin m → ℝ => Z k * Z l)
        = fun Z => ∏ i, (if i = k then Z i else 1) * (if i = l then Z i else 1) := by
      funext Z
      rw [Finset.prod_mul_distrib]
      simp
    rw [e, gbox_std, integral_fintype_prod_eq_prod
      (f := fun i (x : ℝ) => (if i = k then x else 1) * (if i = l then x else 1))]
    refine Finset.prod_eq_zero (mem_univ k) ?_
    simp [h, integral_id_gaussianReal]

lemma gbox_clm_apply {m : ℕ} {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (T : (Fin m → ℝ) →L[ℝ] F) (Z : Fin m → ℝ) : T Z = ∑ k, Z k • T (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single Z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul]
  congr 1
  ext i
  simp [Pi.single_apply]

lemma gbox_clm_coord {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (Z : Fin m → ℝ) (j : Fin d) :
    T Z j = ∑ k, Z k * T (Pi.single k 1) j := by
  rw [gbox_clm_apply T Z]
  simp [Finset.sum_apply]

lemma gbox_clm_coord_fun {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (j : Fin d) :
    (fun Z => T Z j) = fun Z => ∑ k, Z k * T (Pi.single k 1) j :=
  funext fun Z => gbox_clm_coord T Z j

lemma gbox_memLp_clm {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (j : Fin d) (p : ENNReal)
    (hp : p ≠ ⊤) : MemLp (fun Z => T Z j) p (gbox_std m) := by
  rw [gbox_clm_coord_fun T j]
  exact memLp_finsetSum _ fun k _ => (gbox_memLp_coord m k p hp).mul_const _

/-- Linear images of standard normal vectors are centered. -/
lemma gbox_integral_map_coord {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (j : Fin d) :
    ∫ x, x j ∂((gbox_std m).map T) = 0 := by
  rw [integral_map T.measurable.aemeasurable (measurable_pi_apply j).aestronglyMeasurable,
    gbox_clm_coord_fun T j]
  rw [integral_finsetSum _ fun k _ =>
    ((gbox_memLp_coord m k 1 ENNReal.one_ne_top).integrable le_rfl).mul_const _]
  simp [integral_mul_const, gbox_integral_coord]

/-- The covariance of a linear image of a standard normal vector. -/
lemma gbox_integral_map_mul {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (j l : Fin d) :
    ∫ x, x j * x l ∂((gbox_std m).map T)
      = ∑ k, T (Pi.single k 1) j * T (Pi.single k 1) l := by
  rw [integral_map (f := fun x : Fin d → ℝ => x j * x l) T.measurable.aemeasurable
    ((measurable_pi_apply j).mul (measurable_pi_apply l)).aestronglyMeasurable]
  have e0 : (fun Z => T Z j * T Z l) = fun Z => ∑ k, ∑ k',
      Z k * T (Pi.single k 1) j * (Z k' * T (Pi.single k' 1) l) := by
    funext Z
    rw [gbox_clm_coord T Z j, gbox_clm_coord T Z l, Finset.sum_mul_sum]
  rw [e0]
  have hint : ∀ k k' : Fin m, Integrable (fun Z : Fin m → ℝ =>
      Z k * T (Pi.single k 1) j * (Z k' * T (Pi.single k' 1) l)) (gbox_std m) := by
    intro k k'
    have h2 := (gbox_memLp_coord m k 2 (by simp)).integrable_mul
      (gbox_memLp_coord m k' 2 (by simp))
    refine (h2.mul_const (T (Pi.single k 1) j * T (Pi.single k' 1) l)).congr
      (ae_of_all _ fun Z => ?_)
    simp only [Pi.mul_apply]
    ring
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun k' _ => hint k k']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun k' _ => hint k k']
  have e : ∀ k' : Fin m, ∫ Z, Z k * T (Pi.single k 1) j * (Z k' * T (Pi.single k' 1) l)
      ∂(gbox_std m) = (if k = k' then 1 else 0) * (T (Pi.single k 1) j * T (Pi.single k' 1) l) := by
    intro k'
    rw [← gbox_integral_coord_mul m k k', ← integral_mul_const]
    congr 1
    funext Z
    ring
  simp_rw [e]
  simp

/-- Third absolute moments of linear images of standard normal vectors are finite. -/
lemma gbox_integrable_cube {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) :
    Integrable (fun x : Fin d → ℝ => (∑ j, |x j|) ^ 3) ((gbox_std m).map T) := by
  have hmeas : Measurable (fun x : Fin d → ℝ => (∑ j, |x j|) ^ 3) := by fun_prop
  rw [integrable_map_measure hmeas.aestronglyMeasurable T.measurable.aemeasurable]
  have hM : MemLp (fun Z => ∑ j, |T Z j|) ((3 : ℕ) : ENNReal) (gbox_std m) :=
    memLp_finsetSum _ fun j _ => (gbox_memLp_clm T j _ (by simp)).abs
  refine hM.integrable_norm_pow'.congr (ae_of_all _ fun Z => ?_)
  simp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]

/-! ### The scaled summand law: moments -/

lemma gbox_sumLaw_coord {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (B : ℕ) (j : Fin d) :
    ∫ x, x j ∂(gbox_sumLaw T B) = 0 :=
  gbox_integral_map_coord _ j

/-- Second moments of the scaled summand law. -/
lemma gbox_sumLaw_mul {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) {B : ℕ} (hB : 0 < B)
    (j l : Fin d) :
    ∫ x, x j * x l ∂(gbox_sumLaw T B) = (∫ x, x j * x l ∂((gbox_std m).map T)) / B := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : (Real.sqrt B)⁻¹ * (Real.sqrt B)⁻¹ = 1 / B := by
    rw [← mul_inv, Real.mul_self_sqrt hB'.le, one_div]
  rw [gbox_sumLaw, gbox_integral_map_mul, gbox_integral_map_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
  calc (Real.sqrt B)⁻¹ * T (Pi.single k 1) j * ((Real.sqrt B)⁻¹ * T (Pi.single k 1) l)
      = ((Real.sqrt B)⁻¹ * (Real.sqrt B)⁻¹) * (T (Pi.single k 1) j * T (Pi.single k 1) l) := by
        ring
    _ = _ := by rw [hs]; ring

lemma gbox_sumLaw_integrable_cube {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (B : ℕ) :
    Integrable (fun x : Fin d → ℝ => (∑ j, |x j|) ^ 3) (gbox_sumLaw T B) :=
  gbox_integrable_cube _

/-- The third absolute moment of the law of `T Z`. -/
def gbox_C3 {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) : ℝ :=
  ∫ x, (∑ j, |x j|) ^ 3 ∂((gbox_std m).map T)

/-- Third absolute moments of the scaled summand law: `C₃ / B^{3/2}`. -/
lemma gbox_sumLaw_cube {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (B : ℕ) :
    ∫ x, (∑ j, |x j|) ^ 3 ∂(gbox_sumLaw T B) = gbox_C3 T / Real.sqrt B ^ 3 := by
  have hmeas : Measurable (fun x : Fin d → ℝ => (∑ j, |x j|) ^ 3) := by fun_prop
  rw [gbox_sumLaw, gbox_C3, integral_map (by fun_prop) hmeas.aestronglyMeasurable,
    integral_map T.measurable.aemeasurable hmeas.aestronglyMeasurable, ← integral_div]
  congr 1
  funext Z
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow]
  ring

lemma gbox_C3_nonneg {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) : 0 ≤ gbox_C3 T :=
  integral_nonneg fun _ => pow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _

/-! ### The six-dimensional representation -/

/-- The common coefficient `c₁ = 1/64`. -/
def gbox_c1 : ℝ := 1 / 64

/-- The individual coefficient `c₂ = 23/320`. -/
def gbox_c2 : ℝ := 23 / 320

lemma gbox_c2_pos : 0 < gbox_c2 := by norm_num [gbox_c2]

lemma gbox_sqrt_c1 : Real.sqrt gbox_c1 = 1 / 8 := by
  rw [show gbox_c1 = (1 / 8) ^ 2 by norm_num [gbox_c1]]
  exact Real.sqrt_sq (by norm_num)

/-- The input of the pattern of coordinate `p` (patterns `10, 01, 11` are `1, 2, 3`). -/
def gbox_sh (p : Fin 6) : Fin 12 := ⟨p.val % 3 + 1, by omega⟩

/-- The individual input of unit `p / 3` at the pattern of `p`. -/
def gbox_own (p : Fin 6) : Fin 12 := ⟨4 + 4 * (p.val / 3) + (p.val % 3 + 1), by omega⟩

/-- The individual input of unit `p / 3` at the pattern `00`. -/
def gbox_base (p : Fin 6) : Fin 12 := ⟨4 + 4 * (p.val / 3), by omega⟩

/-- The six coordinates `η_i(t) = √c₁ (Z_t - Z_00) + √c₂ (Z_{i,t} - Z_{i,00})`; coordinate `p`
is unit `p / 3` and pattern `p % 3 + 1`. -/
def gbox_eta (Z : Fin 12 → ℝ) (p : Fin 6) : ℝ :=
  Real.sqrt gbox_c1 * (Z (gbox_sh p) - Z 0) + Real.sqrt gbox_c2 * (Z (gbox_own p) - Z (gbox_base p))

/-- The representation map as a continuous linear map. -/
def gbox_T6 : (Fin 12 → ℝ) →L[ℝ] (Fin 6 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := gbox_eta
      map_add' := fun Z Z' => by funext p; simp only [gbox_eta, Pi.add_apply]; ring
      map_smul' := fun c Z => by
        funext p; simp only [gbox_eta, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

@[simp] lemma gbox_T6_apply (Z : Fin 12 → ℝ) (p : Fin 6) : gbox_T6 Z p = gbox_eta Z p := rfl

/-- The limit covariance `Γ∞[(i,t),(j,u)] = c₁([t=u]+1) + c₂[i=j]([t=u]+1)`. -/
def gbox_Gam (p q : Fin 6) : ℝ :=
  gbox_c1 * ((if p.val % 3 = q.val % 3 then 1 else 0) + 1)
    + gbox_c2 * (if p.val / 3 = q.val / 3 then 1 else 0) * ((if p.val % 3 = q.val % 3 then 1 else 0) + 1)

/-- The limit law of the six cause-side differences. -/
def gbox_G6 : Measure (Fin 6 → ℝ) := (gbox_std 12).map gbox_T6

instance gbox_G6_prob : IsProbabilityMeasure gbox_G6 := by unfold gbox_G6; infer_instance

lemma gbox_G6_coord (p : Fin 6) : ∫ x, x p ∂gbox_G6 = 0 := gbox_integral_map_coord _ p

lemma gbox_sum_dd (a b c d : Fin 12) :
    ∑ k : Fin 12, ((if a = k then (1 : ℝ) else 0) - (if b = k then 1 else 0))
      * ((if c = k then (1 : ℝ) else 0) - (if d = k then 1 else 0))
      = (if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0)
        + (if b = d then 1 else 0) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [eq_comm (a := a), eq_comm (a := b)]
  ring

lemma gbox_sum4 (a b c d e f g h : Fin 12) (α β : ℝ) :
    ∑ k : Fin 12, (α * ((if a = k then (1 : ℝ) else 0) - (if b = k then 1 else 0))
        + β * ((if c = k then (1 : ℝ) else 0) - (if d = k then 1 else 0)))
      * (α * ((if e = k then (1 : ℝ) else 0) - (if f = k then 1 else 0))
        + β * ((if g = k then (1 : ℝ) else 0) - (if h = k then 1 else 0)))
      = α * α * ((if a = e then 1 else 0) - (if a = f then 1 else 0) - (if b = e then 1 else 0)
          + (if b = f then 1 else 0))
        + α * β * ((if a = g then 1 else 0) - (if a = h then 1 else 0) - (if b = g then 1 else 0)
          + (if b = h then 1 else 0))
        + β * α * ((if c = e then 1 else 0) - (if c = f then 1 else 0) - (if d = e then 1 else 0)
          + (if d = f then 1 else 0))
        + β * β * ((if c = g then 1 else 0) - (if c = h then 1 else 0) - (if d = g then 1 else 0)
          + (if d = h then 1 else 0)) := by
  rw [← gbox_sum_dd a b e f, ← gbox_sum_dd a b g h, ← gbox_sum_dd c d e f, ← gbox_sum_dd c d g h,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma gbox_T6_single (k : Fin 12) (p : Fin 6) :
    gbox_T6 (Pi.single k 1) p
      = Real.sqrt gbox_c1 * ((if gbox_sh p = k then (1 : ℝ) else 0) - (if (0 : Fin 12) = k then 1 else 0))
        + Real.sqrt gbox_c2 * ((if gbox_own p = k then (1 : ℝ) else 0)
          - (if gbox_base p = k then 1 else 0)) := by
  simp only [gbox_T6_apply, gbox_eta, Pi.single_apply, eq_comm (b := k)]

/-- The covariance of the limit law is `Γ∞`. -/
theorem gbox_integral_G6_mul (p q : Fin 6) : ∫ x, x p * x q ∂gbox_G6 = gbox_Gam p q := by
  rw [gbox_G6, gbox_integral_map_mul]
  simp only [gbox_T6_single]
  rw [gbox_sum4]
  set s := Real.sqrt gbox_c2 with hs
  have hc2 : gbox_c2 = s ^ 2 := (Real.sq_sqrt gbox_c2_pos.le).symm
  rw [gbox_Gam, hc2, gbox_sqrt_c1]
  fin_cases p <;> fin_cases q <;> simp [gbox_sh, gbox_own, gbox_base, gbox_c1] <;> ring

/-- Second moments of one scaled summand of the six-dimensional limit law. -/
lemma gbox_sumLaw6_mul {B : ℕ} (hB : 0 < B) (p q : Fin 6) :
    ∫ x, x p * x q ∂(gbox_sumLaw gbox_T6 B) = gbox_Gam p q / B := by
  rw [gbox_sumLaw_mul _ hB, ← gbox_G6, gbox_integral_G6_mul]

/-! ### Two independent copies -/

lemma gbox_split_cases (j : Fin 12) :
    (∃ p : Fin 6, j = Fin.castAdd 6 p) ∨ ∃ p : Fin 6, j = Fin.natAdd 6 p := by
  by_cases h : j.val < 6
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨j.val - 6, by omega⟩, Fin.ext (by simp; omega)⟩

/-- Concatenation of two six-vectors, as a continuous linear map. -/
def gbox_app : (Fin 6 → ℝ) × (Fin 6 → ℝ) →L[ℝ] (Fin 12 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun xy => Fin.append xy.1 xy.2
      map_add' := fun xy xy' => by
        funext j
        rcases gbox_split_cases j with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
          simp only [Prod.fst_add, Prod.snd_add, Fin.append_left, Fin.append_right, Pi.add_apply]
      map_smul' := fun c xy => by
        funext j
        rcases gbox_split_cases j with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
          simp only [Prod.smul_fst, Prod.smul_snd, Fin.append_left, Fin.append_right,
            Pi.smul_apply, RingHom.id_apply] }

@[simp] lemma gbox_app_left (xy : (Fin 6 → ℝ) × (Fin 6 → ℝ)) (p : Fin 6) :
    gbox_app xy (Fin.castAdd 6 p) = xy.1 p := Fin.append_left _ _ _

@[simp] lemma gbox_app_right (xy : (Fin 6 → ℝ) × (Fin 6 → ℝ)) (p : Fin 6) :
    gbox_app xy (Fin.natAdd 6 p) = xy.2 p := Fin.append_right _ _ _

/-- Splitting twenty-four inputs into two blocks of twelve. -/
def gbox_split : (Fin 24 → ℝ) →L[ℝ] (Fin 12 → ℝ) × (Fin 12 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z => (fun k => Z (Fin.castAdd 12 k), fun k => Z (Fin.natAdd 12 k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The representation of two independent copies: coordinates `castAdd 6 p` are `η_p` of the
first twelve inputs, coordinates `natAdd 6 p` are `η_p` of the last twelve inputs. -/
def gbox_T12 : (Fin 24 → ℝ) →L[ℝ] (Fin 12 → ℝ) :=
  gbox_app.comp ((gbox_T6.prodMap gbox_T6).comp gbox_split)

@[simp] lemma gbox_T12_left (Z : Fin 24 → ℝ) (p : Fin 6) :
    gbox_T12 Z (Fin.castAdd 6 p) = gbox_eta (fun k => Z (Fin.castAdd 12 k)) p := by
  show gbox_app ((gbox_T6.prodMap gbox_T6) (gbox_split Z)) (Fin.castAdd 6 p) = _
  rw [gbox_app_left]; rfl

@[simp] lemma gbox_T12_right (Z : Fin 24 → ℝ) (p : Fin 6) :
    gbox_T12 Z (Fin.natAdd 6 p) = gbox_eta (fun k => Z (Fin.natAdd 12 k)) p := by
  show gbox_app ((gbox_T6.prodMap gbox_T6) (gbox_split Z)) (Fin.natAdd 6 p) = _
  rw [gbox_app_right]; rfl

/-- The limit law of two independent copies of the six cause-side differences. -/
def gbox_G12 : Measure (Fin 12 → ℝ) := (gbox_std 24).map gbox_T12

instance gbox_G12_prob : IsProbabilityMeasure gbox_G12 := by unfold gbox_G12; infer_instance

lemma gbox_G12_coord (j : Fin 12) : ∫ x, x j ∂gbox_G12 = 0 := gbox_integral_map_coord _ j

/-- The block-diagonal covariance of two independent copies. -/
def gbox_Gam12 (j l : Fin 12) : ℝ :=
  Fin.append (fun p => Fin.append (gbox_Gam p) (0 : Fin 6 → ℝ))
    (fun p => Fin.append (0 : Fin 6 → ℝ) (gbox_Gam p)) j l

@[simp] lemma gbox_Gam12_ll (p q : Fin 6) :
    gbox_Gam12 (Fin.castAdd 6 p) (Fin.castAdd 6 q) = gbox_Gam p q := by
  simp only [gbox_Gam12, Fin.append_left]

@[simp] lemma gbox_Gam12_lr (p q : Fin 6) :
    gbox_Gam12 (Fin.castAdd 6 p) (Fin.natAdd 6 q) = 0 := by
  simp only [gbox_Gam12, Fin.append_left, Fin.append_right, Pi.zero_apply]

@[simp] lemma gbox_Gam12_rl (p q : Fin 6) :
    gbox_Gam12 (Fin.natAdd 6 p) (Fin.castAdd 6 q) = 0 := by
  simp only [gbox_Gam12, Fin.append_left, Fin.append_right, Pi.zero_apply]

@[simp] lemma gbox_Gam12_rr (p q : Fin 6) :
    gbox_Gam12 (Fin.natAdd 6 p) (Fin.natAdd 6 q) = gbox_Gam p q := by
  simp only [gbox_Gam12, Fin.append_right]

lemma gbox_single_castAdd (k : Fin 12) :
    (fun k' : Fin 12 => (Pi.single (Fin.castAdd 12 k) (1 : ℝ) : Fin 24 → ℝ) (Fin.castAdd 12 k'))
      = Pi.single k 1 := by
  funext k'
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]

lemma gbox_single_castAdd' (k : Fin 12) :
    (fun k' : Fin 12 => (Pi.single (Fin.castAdd 12 k) (1 : ℝ) : Fin 24 → ℝ) (Fin.natAdd 12 k')) = 0 := by
  funext k'
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Pi.zero_apply]
  exact ite_eq_right_iff.2 fun h => absurd h (by omega)

lemma gbox_single_natAdd (k : Fin 12) :
    (fun k' : Fin 12 => (Pi.single (Fin.natAdd 12 k) (1 : ℝ) : Fin 24 → ℝ) (Fin.natAdd 12 k'))
      = Pi.single k 1 := by
  funext k'
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_natAdd]
  congr 1
  exact propext ⟨fun h => by omega, fun h => by omega⟩

lemma gbox_single_natAdd' (k : Fin 12) :
    (fun k' : Fin 12 => (Pi.single (Fin.natAdd 12 k) (1 : ℝ) : Fin 24 → ℝ) (Fin.castAdd 12 k')) = 0 := by
  funext k'
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Pi.zero_apply]
  exact ite_eq_right_iff.2 fun h => absurd h (by omega)

lemma gbox_eta_zero : gbox_eta 0 = 0 := by
  funext p; simp [gbox_eta]

lemma gbox_T12_single_castAdd (k : Fin 12) :
    gbox_T12 (Pi.single (Fin.castAdd 12 k) 1) = gbox_app (gbox_T6 (Pi.single k 1), 0) := by
  funext j
  rcases gbox_split_cases j with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [gbox_T12_left, gbox_single_castAdd, gbox_app_left]; rfl
  · rw [gbox_T12_right, gbox_single_castAdd', gbox_app_right, gbox_eta_zero]

lemma gbox_T12_single_natAdd (k : Fin 12) :
    gbox_T12 (Pi.single (Fin.natAdd 12 k) 1) = gbox_app (0, gbox_T6 (Pi.single k 1)) := by
  funext j
  rcases gbox_split_cases j with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [gbox_T12_left, gbox_single_natAdd', gbox_app_left, gbox_eta_zero]
  · rw [gbox_T12_right, gbox_single_natAdd, gbox_app_right]; rfl

lemma gbox_sum24 (f : Fin 24 → ℝ) :
    ∑ k, f k = ∑ k : Fin 12, f (Fin.castAdd 12 k) + ∑ k : Fin 12, f (Fin.natAdd 12 k) :=
  Fin.sum_univ_add (a := 12) (b := 12) f

lemma gbox_sum_T6 (p q : Fin 6) :
    ∑ k, gbox_T6 (Pi.single k 1) p * gbox_T6 (Pi.single k 1) q = gbox_Gam p q := by
  rw [← gbox_integral_map_mul, ← gbox_G6, gbox_integral_G6_mul]

/-- The covariance of two independent copies is block diagonal. -/
theorem gbox_integral_G12_mul (j l : Fin 12) : ∫ x, x j * x l ∂gbox_G12 = gbox_Gam12 j l := by
  rw [gbox_G12, gbox_integral_map_mul, gbox_sum24]
  simp only [gbox_T12_single_castAdd, gbox_T12_single_natAdd]
  rcases gbox_split_cases j with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
  rcases gbox_split_cases l with ⟨q, rfl⟩ | ⟨q, rfl⟩ <;>
    simp only [gbox_app_left, gbox_app_right, gbox_Gam12_ll, gbox_Gam12_lr, gbox_Gam12_rl,
      gbox_Gam12_rr, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      zero_add, gbox_sum_T6]

/-- Second moments of one scaled summand of the twelve-dimensional limit law. -/
lemma gbox_sumLaw12_mul {B : ℕ} (hB : 0 < B) (j l : Fin 12) :
    ∫ x, x j * x l ∂(gbox_sumLaw gbox_T12 B) = gbox_Gam12 j l / B := by
  rw [gbox_sumLaw_mul _ hB, ← gbox_G12, gbox_integral_G12_mul]

/-- The twelve-dimensional limit law is the law of two independent copies of the six-dimensional
one. -/
theorem gbox_G12_eq : gbox_G12 = (gbox_G6.prod gbox_G6).map gbox_app := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [gbox_G12, gbox_charFunDual_map, charFunDual_map, charFunDual_prod, gbox_G6,
    gbox_charFunDual_map, gbox_charFunDual_map, ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_add]
  congr 1
  rw [gbox_sum24 (fun k => (L (gbox_T12 (Pi.single k 1))) ^ 2)]
  simp only [gbox_T12_single_castAdd, gbox_T12_single_natAdd, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  ring

lemma gbox_measurable_halves :
    Measurable (fun x : Fin 12 → ℝ =>
      ((fun p : Fin 6 => x (Fin.castAdd 6 p)), fun p : Fin 6 => x (Fin.natAdd 6 p))) := by
  fun_prop

/-- Events of the two halves are independent under the twelve-dimensional limit law. -/
theorem gbox_G12_prod (A A' : Set (Fin 6 → ℝ)) (hA : MeasurableSet A) (hA' : MeasurableSet A') :
    gbox_G12 {x | (fun p => x (Fin.castAdd 6 p)) ∈ A ∧ (fun p => x (Fin.natAdd 6 p)) ∈ A'}
      = gbox_G6 A * gbox_G6 A' := by
  have hmeas : MeasurableSet
      {x : Fin 12 → ℝ | (fun p => x (Fin.castAdd 6 p)) ∈ A ∧ (fun p => x (Fin.natAdd 6 p)) ∈ A'} :=
    gbox_measurable_halves (hA.prod hA')
  rw [gbox_G12_eq, Measure.map_apply gbox_app.measurable hmeas, ← Measure.prod_prod]
  congr 1
  ext xy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, gbox_app_left, gbox_app_right]

lemma gbox_G12_prod_real (A A' : Set (Fin 6 → ℝ)) (hA : MeasurableSet A)
    (hA' : MeasurableSet A') :
    gbox_G12.real {x | (fun p => x (Fin.castAdd 6 p)) ∈ A ∧ (fun p => x (Fin.natAdd 6 p)) ∈ A'}
      = gbox_G6.real A * gbox_G6.real A' := by
  simp only [measureReal_def, gbox_G12_prod A A' hA hA', ENNReal.toReal_mul]

lemma gbox_measurableSet_orthant {n : ℕ} (c : Fin n → ℝ) :
    MeasurableSet {y : Fin n → ℝ | ∀ p, y p ≤ c p} := by
  have e : {y : Fin n → ℝ | ∀ p, y p ≤ c p} = Set.univ.pi fun p => Set.Iic (c p) := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
    exact Iff.rfl
  rw [e]
  exact MeasurableSet.univ_pi fun p => measurableSet_Iic

/-- Orthants of the twelve-dimensional limit law factor into orthants of the two halves. -/
theorem gbox_G12_orthant (c : Fin 12 → ℝ) :
    gbox_G12.real {x | ∀ j, x j ≤ c j}
      = gbox_G6.real {x | ∀ p, x p ≤ c (Fin.castAdd 6 p)}
        * gbox_G6.real {x | ∀ p, x p ≤ c (Fin.natAdd 6 p)} := by
  rw [← gbox_G12_prod_real _ _ (gbox_measurableSet_orthant _) (gbox_measurableSet_orthant _)]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨fun p => h _, fun p => h _⟩
  · rintro ⟨h1, h2⟩ j
    rcases gbox_split_cases j with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact h1 p
    · exact h2 p

/-! ### Slab upper bounds -/

/-- A linear functional of a standard normal vector is a centered real Gaussian. -/
lemma gbox_std_map_functional {m : ℕ} (T : (Fin m → ℝ) →L[ℝ] ℝ) :
    (gbox_std m).map T = gaussianReal 0 (∑ k, (T (Pi.single k 1)) ^ 2).toNNReal := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [gbox_charFunDual_map, charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  have hL : ∀ x : ℝ, L x = x * L 1 := fun x => by simpa using L.map_smul x 1
  have key : ∑ k, (L (T (Pi.single k 1))) ^ 2 = (L 1) ^ 2 * ∑ k, (T (Pi.single k 1)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hL (T (Pi.single k 1))]
    ring
  rw [key, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _),
    Real.coe_toNNReal _ (Finset.sum_nonneg fun k _ => sq_nonneg _), map_zero]
  push_cast
  ring_nf

lemma gbox_gauss_Icc_le {v : NNReal} (hv : v ≠ 0) (c w : ℝ) (hw : 0 ≤ w) :
    (gaussianReal 0 v).real (Set.Icc c (c + w)) ≤ w * (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ hv,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc fun x _ =>
      gaussianPDFReal_nonneg _ _ _)]
  refine (Real.le_norm_self _).trans ((norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
    (C := (Real.sqrt (2 * Real.pi * v))⁻¹) fun x _ => ?_).trans ?_)
  · rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal]
    refine mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) ?_
    refine Real.exp_le_one_iff.2 ?_
    have : (0 : ℝ) ≤ 2 * v := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) this
  · rw [Real.volume_real_Icc_of_le (by linarith), add_sub_cancel_left, mul_comm]

/-- Slab bound for a coordinate of a linear image of a standard normal vector whose variance is at
least `v0`. -/
lemma gbox_slab_generic {m d : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (j : Fin d) {v0 : ℝ}
    (hv0 : 0 < v0) (hv : v0 ≤ ∑ k, (T (Pi.single k 1) j) ^ 2) (c w : ℝ) (hw : 0 ≤ w) :
    ((gbox_std m).map T).real {x | x j ∈ Set.Icc c (c + w)}
      ≤ w / (Real.sqrt v0 * Real.sqrt (2 * Real.pi)) := by
  have hset : {x : Fin d → ℝ | x j ∈ Set.Icc c (c + w)} = (fun x => x j) ⁻¹' Set.Icc c (c + w) :=
    rfl
  rw [hset, ← map_measureReal_apply (measurable_pi_apply j) measurableSet_Icc,
    Measure.map_map (measurable_pi_apply j) T.measurable]
  have hc : (fun x : Fin d → ℝ => x j) ∘ T = ⇑((ContinuousLinearMap.proj j).comp T) := rfl
  rw [hc, gbox_std_map_functional]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  set v := ∑ k, (T (Pi.single k 1) j) ^ 2 with hvdef
  have hvpos : 0 < v := hv0.trans_le hv
  have hne : v.toNNReal ≠ 0 := by simpa using hvpos
  refine (gbox_gauss_Icc_le hne c w hw).trans ?_
  rw [Real.coe_toNNReal _ hvpos.le, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hw
  refine inv_anti₀ (by positivity) ?_
  rw [mul_comm (Real.sqrt v0), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])

lemma gbox_Gam_diag (p : Fin 6) : gbox_Gam p p = 2 * gbox_c1 + 2 * gbox_c2 := by
  simp only [gbox_Gam, ite_true]
  ring

lemma gbox_c2_le_Gam (p : Fin 6) : gbox_c2 ≤ gbox_Gam p p := by
  rw [gbox_Gam_diag]
  norm_num [gbox_c1, gbox_c2]

/-- Slab bound for the six-dimensional limit law. -/
theorem gbox_G6_slab_le (p : Fin 6) (c w : ℝ) (hw : 0 ≤ w) :
    gbox_G6.real {x | x p ∈ Set.Icc c (c + w)}
      ≤ w / (Real.sqrt gbox_c2 * Real.sqrt (2 * Real.pi)) := by
  refine gbox_slab_generic gbox_T6 p gbox_c2_pos ?_ c w hw
  have := gbox_sum_T6 p p
  simp only [← sq] at this
  rw [this]
  exact gbox_c2_le_Gam p

lemma gbox_sum_T12 (j : Fin 12) :
    ∑ k, (gbox_T12 (Pi.single k 1) j) ^ 2 = gbox_Gam12 j j := by
  rw [← gbox_integral_G12_mul, gbox_G12, gbox_integral_map_mul]
  simp only [sq]

lemma gbox_c2_le_Gam12 (j : Fin 12) : gbox_c2 ≤ gbox_Gam12 j j := by
  rcases gbox_split_cases j with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [gbox_Gam12_ll]; exact gbox_c2_le_Gam p
  · rw [gbox_Gam12_rr]; exact gbox_c2_le_Gam p

/-- Slab bound for the twelve-dimensional limit law. -/
theorem gbox_G12_slab_le (j : Fin 12) (c w : ℝ) (hw : 0 ≤ w) :
    gbox_G12.real {x | x j ∈ Set.Icc c (c + w)}
      ≤ w / (Real.sqrt gbox_c2 * Real.sqrt (2 * Real.pi)) := by
  refine gbox_slab_generic gbox_T12 j gbox_c2_pos ?_ c w hw
  rw [gbox_sum_T12]
  exact gbox_c2_le_Gam12 j

/-! ### Box lower bounds -/

lemma gbox_gauss_Icc_ge (a b M : ℝ) (hab : a ≤ b) (hM : ∀ x ∈ Set.Icc a b, x ^ 2 ≤ M) :
    (b - a) * (Real.exp (-M / 2) / Real.sqrt (2 * Real.pi))
      ≤ (gaussianReal 0 1).real (Set.Icc a b) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc fun x _ =>
      gaussianPDFReal_nonneg _ _ _)]
  have h := setIntegral_ge_of_const_le_real (μ := volume) (s := Set.Icc a b)
    (f := gaussianPDFReal 0 1)
    (c := Real.exp (-M / 2) / Real.sqrt (2 * Real.pi)) measurableSet_Icc measure_Icc_lt_top.ne
    (fun x hx => ?_) (integrable_gaussianPDFReal 0 1).integrableOn
  · rwa [Real.volume_real_Icc_of_le hab, mul_comm] at h
  · rw [gaussianPDFReal, div_eq_mul_inv, mul_comm]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (inv_nonneg.2 (Real.sqrt_nonneg _))
    have := hM x hx
    linarith

/-- The box of inputs used for the lower bound: the four shared inputs in `[0, 1]`, the two
individual inputs at pattern `00` in `[3u, 3u + 1]`, the six other individual inputs in
`[-u - 1, -u]`. -/
def gbox_boxI (u : ℝ) (k : Fin 12) : Set ℝ :=
  if k.val < 4 then Set.Icc 0 1
  else if k.val = 4 ∨ k.val = 8 then Set.Icc (3 * u) (3 * u + 1) else Set.Icc (-u - 1) (-u)

/-- The one-dimensional lower bounds for the box. -/
def gbox_boxL (u : ℝ) (k : Fin 12) : ℝ :=
  if k.val < 4 then Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi)
  else if k.val = 4 ∨ k.val = 8 then Real.exp (-(3 * u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi)
  else Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi)

lemma gbox_boxL_nonneg (u : ℝ) (k : Fin 12) : 0 ≤ gbox_boxL u k := by
  unfold gbox_boxL
  split_ifs <;> positivity

lemma gbox_boxL_le {u : ℝ} (hu : 0 ≤ u) (k : Fin 12) :
    gbox_boxL u k ≤ (gaussianReal 0 1).real (gbox_boxI u k) := by
  unfold gbox_boxL gbox_boxI
  split_ifs
  · have h := gbox_gauss_Icc_ge 0 1 1 zero_le_one fun x hx => by nlinarith [hx.1, hx.2]
    rwa [sub_zero, one_mul] at h
  · have h := gbox_gauss_Icc_ge (3 * u) (3 * u + 1) ((3 * u + 1) ^ 2) (by linarith)
      fun x hx => by nlinarith [hx.1, hx.2]
    rwa [show 3 * u + 1 - 3 * u = (1 : ℝ) by ring, one_mul] at h
  · have h := gbox_gauss_Icc_ge (-u - 1) (-u) ((u + 1) ^ 2) (by linarith)
      fun x hx => by nlinarith [hx.1, hx.2]
    rwa [show -u - (-u - 1) = (1 : ℝ) by ring, one_mul] at h

/-- The constant of the box lower bound, `e^{-2} / (2π)^6`. -/
def gbox_c0 : ℝ := Real.exp (-2) / (2 * Real.pi) ^ 6

lemma gbox_c0_pos : 0 < gbox_c0 := by unfold gbox_c0; positivity

lemma gbox_prod_boxL (u : ℝ) :
    ∏ k, gbox_boxL u k = gbox_c0 * Real.exp (-(12 * u ^ 2 + 12 * u + 4)) := by
  have e : ∏ k, gbox_boxL u k
      = (Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi)) ^ 4
        * (Real.exp (-(3 * u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) ^ 2
        * (Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) ^ 6 := by
    simp [Fin.prod_univ_succ, gbox_boxL]
    ring
  have hs : Real.sqrt (2 * Real.pi) ^ 12 = (2 * Real.pi) ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 by rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [e]
  calc (Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi)) ^ 4
        * (Real.exp (-(3 * u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) ^ 2
        * (Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) ^ 6
      = Real.exp (-1 / 2) ^ 4 * Real.exp (-(3 * u + 1) ^ 2 / 2) ^ 2
          * Real.exp (-(u + 1) ^ 2 / 2) ^ 6 / Real.sqrt (2 * Real.pi) ^ 12 := by ring
    _ = Real.exp (-(12 * u ^ 2 + 12 * u + 6)) / (2 * Real.pi) ^ 6 := by
        rw [hs, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add,
          ← Real.exp_add]
        congr 2
        push_cast
        ring
    _ = gbox_c0 * Real.exp (-(12 * u ^ 2 + 12 * u + 4)) := by
        rw [gbox_c0, div_mul_eq_mul_div, ← Real.exp_add]
        congr 2
        ring

lemma gbox_eta_le_of_mem {u y : ℝ} (hu : Real.sqrt gbox_c2 * (4 * u) = 2 * y + 1)
    {Z : Fin 12 → ℝ} (hZ : ∀ k, Z k ∈ gbox_boxI u k) (p : Fin 6) :
    gbox_eta Z p ≤ -2 * y - 7 / 8 := by
  have hp := p.isLt
  have h1 := hZ (gbox_sh p)
  rw [gbox_boxI, ite_eq_left (show (gbox_sh p).val < 4 by simp only [gbox_sh]; omega)] at h1
  have h0 := hZ 0
  rw [gbox_boxI, ite_eq_left (show (0 : Fin 12).val < 4 by decide)] at h0
  have ho := hZ (gbox_own p)
  rw [gbox_boxI, ite_eq_right (show ¬ (gbox_own p).val < 4 by simp only [gbox_own]; omega),
    ite_eq_right (show ¬ ((gbox_own p).val = 4 ∨ (gbox_own p).val = 8) by simp only [gbox_own]; omega)]
    at ho
  have hb := hZ (gbox_base p)
  rw [gbox_boxI, ite_eq_right (show ¬ (gbox_base p).val < 4 by simp only [gbox_base]; omega),
    ite_eq_left (show (gbox_base p).val = 4 ∨ (gbox_base p).val = 8 by simp only [gbox_base]; omega)]
    at hb
  have hc2 : 0 < Real.sqrt gbox_c2 := Real.sqrt_pos.2 gbox_c2_pos
  have hdiff : Z (gbox_own p) - Z (gbox_base p) ≤ -(4 * u) := by linarith [ho.2, hb.1]
  have h2 : Real.sqrt gbox_c2 * (Z (gbox_own p) - Z (gbox_base p)) ≤ -(2 * y + 1) := by
    rw [← hu, ← mul_neg]
    exact mul_le_mul_of_nonneg_left hdiff hc2.le
  rw [gbox_eta, gbox_sqrt_c1]
  linarith [h1.2, h0.1]

/-- Box lower bound: with `u = (2y + 1)/(4 √c₂)`, the negative orthant at level `-2y - ε` has
probability at least `c₀ e^{-(12u² + 12u + 4)}` under the limit law. -/
theorem gbox_G6_box_ge {y ε : ℝ} (hy : 0 ≤ y) (hε : ε ≤ 7 / 8) :
    gbox_c0 * Real.exp (-(12 * ((2 * y + 1) / (4 * Real.sqrt gbox_c2)) ^ 2
        + 12 * ((2 * y + 1) / (4 * Real.sqrt gbox_c2)) + 4))
      ≤ gbox_G6.real {x | ∀ p, x p ≤ -2 * y - ε} := by
  set u := (2 * y + 1) / (4 * Real.sqrt gbox_c2) with hudef
  have hc2 : 0 < Real.sqrt gbox_c2 := Real.sqrt_pos.2 gbox_c2_pos
  have hu : Real.sqrt gbox_c2 * (4 * u) = 2 * y + 1 := by
    rw [hudef]; field_simp
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  rw [gbox_G6, map_measureReal_apply gbox_T6.measurable (gbox_measurableSet_orthant _)]
  refine le_trans ?_ (measureReal_mono (s₁ := Set.univ.pi (gbox_boxI u)) ?_)
  · have e : (gbox_std 12).real (Set.univ.pi (gbox_boxI u))
        = ∏ k, (gaussianReal 0 1).real (gbox_boxI u k) := by
      simp only [measureReal_def, gbox_std, Measure.pi_pi, ENNReal.toReal_prod]
    rw [e, ← gbox_prod_boxL]
    exact Finset.prod_le_prod (fun k _ => gbox_boxL_nonneg u k) fun k _ => gbox_boxL_le hu0 k
  · intro Z hZ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, gbox_T6_apply]
    intro p
    have := gbox_eta_le_of_mem hu (fun k => hZ k (Set.mem_univ k)) p
    linarith

lemma gbox_two_pi_pow_le : (2 * Real.pi) ^ 6 ≤ Real.exp 12 := by
  have h1 : 2 * Real.pi ≤ Real.exp 2 := by
    have := Real.exp_one_gt_d9
    have hp := Real.pi_lt_d2
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  calc (2 * Real.pi) ^ 6 ≤ Real.exp 2 ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
    _ = Real.exp 12 := by rw [← Real.exp_nat_mul]; norm_num

lemma gbox_arith (s : ℝ) (hs : 300 ≤ s) :
    240 / 23 * (2 * (7 / 50 * s) + 1) ^ 2 + 12 * (2 * (7 / 50 * s) + 1) + 18 ≤ 17 / 20 * s ^ 2 := by
  nlinarith [mul_self_nonneg (s - 300)]

/-- With `y = yN N`, the box probability is eventually at least `N^{-17/20}`. -/
theorem gbox_eventually_G6_box :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ ε : ℝ, ε ≤ 7 / 8 →
      (N : ℝ) ^ (-(17 / 20 : ℝ)) ≤ gbox_G6.real {x | ∀ p, x p ≤ -2 * yN N - ε} := by
  have ht : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 90000, Filter.eventually_ge_atTop 1] with N hN hN1 ε hε
  refine le_trans ?_ (gbox_G6_box_ge (yN_nonneg N) hε)
  set L := Real.log N with hL
  set s := Real.sqrt L with hsdef
  have hL0 : 0 ≤ L := by linarith
  have hs300 : 300 ≤ s := by
    rw [hsdef, show (300 : ℝ) = Real.sqrt (300 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsL : s ^ 2 = L := Real.sq_sqrt hL0
  have hy : yN N = 7 / 50 * s := by rw [yN, gamT]
  set u := (2 * yN N + 1) / (4 * Real.sqrt gbox_c2) with hudef
  have hc2 : 0 < Real.sqrt gbox_c2 := Real.sqrt_pos.2 gbox_c2_pos
  have hc2sq : Real.sqrt gbox_c2 ^ 2 = 23 / 320 := by rw [Real.sq_sqrt gbox_c2_pos.le, gbox_c2]
  have hc2ge : 1 / 4 ≤ Real.sqrt gbox_c2 := by nlinarith
  have hw : 0 ≤ 2 * yN N + 1 := by linarith [yN_nonneg N]
  have hu2 : u ^ 2 = 20 / 23 * (2 * yN N + 1) ^ 2 := by
    rw [hudef, div_pow, mul_pow, hc2sq]; ring
  have hule : u ≤ 2 * yN N + 1 := by
    rw [hudef, div_le_iff₀ (by positivity)]
    nlinarith
  have hexp : 12 * u ^ 2 + 12 * u + 18 ≤ 17 / 20 * L := by
    rw [← hsL]
    have := gbox_arith s hs300
    rw [hy] at hu2 hule
    nlinarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.rpow_def_of_pos hN0, ← hL]
  calc Real.exp (L * -(17 / 20)) ≤ Real.exp (-(12 * u ^ 2 + 12 * u + 18)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-2) / Real.exp 12 * Real.exp (-(12 * u ^ 2 + 12 * u + 4)) := by
        rw [div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_sub]; ring_nf
    _ ≤ gbox_c0 * Real.exp (-(12 * u ^ 2 + 12 * u + 4)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) gbox_two_pi_pow_le

/-! ### Stability for the two limit laws -/

/-- Gaussian stability for the six-dimensional limit law. -/
theorem gbox_integral_sum_pi_G6 {B : ℕ} (hB : 0 < B) {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f (∑ β, x β) ∂(Measure.pi fun _ : Fin B => gbox_sumLaw gbox_T6 B)
      = ∫ x, f x ∂gbox_G6 := by
  rw [gbox_integral_sum_pi gbox_T6 hB hf, gbox_G6,
    integral_map gbox_T6.measurable.aemeasurable hf.aestronglyMeasurable]

/-- Gaussian stability for the twelve-dimensional limit law. -/
theorem gbox_integral_sum_pi_G12 {B : ℕ} (hB : 0 < B) {f : (Fin 12 → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ x, f (∑ β, x β) ∂(Measure.pi fun _ : Fin B => gbox_sumLaw gbox_T12 B)
      = ∫ x, f x ∂gbox_G12 := by
  rw [gbox_integral_sum_pi gbox_T12 hB hf, gbox_G12,
    integral_map gbox_T12.measurable.aemeasurable hf.aestronglyMeasurable]

/-- A constant-level orthant of the twelve-dimensional limit law is the square of the
six-dimensional one. -/
theorem gbox_G12_box (c : ℝ) :
    gbox_G12.real {x | ∀ j, x j ≤ c} = (gbox_G6.real {x | ∀ p, x p ≤ c}) ^ 2 := by
  rw [gbox_G12_orthant (fun _ => c), sq]

end

end Census
end IIT
