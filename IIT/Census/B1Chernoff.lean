/-
Census of complexes, B1 development, module A4: the Chernoff/Cramér toolkit.

Generic exponential Markov:
* `chernoff_indep` (lower tail, `ENNReal` form), `chernoff_indep_real` (real form, as in the
  blueprint), `chernoff_indep_ge` (upper tail), for independent summands;
* `chernoff_pi`, `chernoff_pi_joint`: on a product measure `Measure.pi`; the joint form has several
  linear constraints `∑ i f k i (x i) ≤ a k` with multipliers `t k ≥ 0` and a coordinatewise window.

The cube:
* `mp_colsOf`, `mp_colOf`, `iIndepFun_cols`: under `cubeM N` the columns `fun r => w r i` are iid
  with law `colLaw N`; `colLaw_map_pair`/`_triple`, `lintegral_colLaw_pair`/`_triple`: entries of
  distinct rows of a column are iid `unif`;
* `cubeM_chernoff_col_sum`, `cubeM_chernoff_cols` (joint Chernoff over the columns),
  `cubeM_chernoff_three` (per-column functions of three rows `ra i, rb i, rc i`);
* `joint_template` (the joint-certificate template of Section 3 of the B1 blueprint), its real
  form `joint_template_real`, and `rate_of_log_le` (per-coordinate log-rate to `e^{-R N}`, with the
  `2^N` of the union over the heavy row); `setLIntegral_Ioc_le_cells` (Riemann cells),
  `setLIntegral_unif_le`.

Closed-form moment generating functions under `unif` (clamped variable `clamp01 U`):
* `lintegral_unif_negLog`: `E e^{t(-log U)} = 1/(1-t)` (`t < 1`);
* `lintegral_unif_rpow`, `lintegral_unif_pow`: `E U^p = 1/(p+1)`;
* `lintegral_unif_logRatio` (`n : ℕ`), `lintegral_unif_logRatio_rpow` (real `λ > -1`):
  `E e^{-λ log(2y/(y+U))} = ((1+y)^{λ+1} - y^{λ+1}) / ((λ+1)(2y)^λ)`;
* `lintegral_unif_logRatioTrunc`: the truncated `V = min (log (2y/(y+U))) (log (y/c))`,
  `E e^{-nV} = (2c-y)(c/y)^n + ((1+y)^{n+1} - (2c)^{n+1}) / ((n+1)(2y)^n)` for `0 ≤ 2c-y ≤ 1`;
* `lintegral_unif_fold_pow`: `E max(U,1-U)^n = 2(1 - 2^{-(n+1)})/(n+1)`;
* `lintegral_unif_exp`: `E e^{tU} = (e^t - 1)/t`.

Cramér for `∑ -log U` (the row weights `XW`, `XMW`):
* `rowM_negLog_chernoff`, `rowM_negLog_sum_le`, `gamma_lower_tail`, `pi_rows_negLog_tail`,
  `cubeM_rows_negLog_tail`, `min_rows_tail`; `cubeM_card_rows_ge` and `cubeM_many_light_rows`
  (at least `K` light rows, for C11).

Type event: `type_event_ge` (and `type_event_ge_rowM`, `type_event_ge_Ico`), via the multinomial
count `fibTypeCount_mul_prod_factorial` and `pow_le_fibTypeCount` (`N^N ≤ (N+1)^k #T(n) ∏ n_j^{n_j}`);
`cubeM_two_rows` (events of two distinct rows are independent).

Rational bounds: `exp_le_rat`, `rat_le_exp`, `log_le_rat`, `log_ge_rat` through `Real.exp_bound`
(the hypotheses are rational inequalities on `expTay`, `expErr`, checkable by `decide +kernel`, see
`log_three_halves_bounds`).

Deviations from the blueprint statements (A4), all minimal:
* `chernoff_indep` is stated in `ENNReal` (`μ S ≤ ofReal (exp (λ a)) * ∏ ∫⁻ ofReal (exp (-λ X i))`),
  which needs no integrability; the literal real form is `chernoff_indep_real` (integrability of
  `exp (-λ X i)` added as hypothesis). Measurability of the `X i` is assumed.
* `min_rows_tail` is stated with the explicit sum `∑ i, -Real.log (clamp01 (w r i))` (this is
  `XW w r` of B1Defs, which is not imported); the rate needs `0 < x ≤ N`.
* `type_event_ge` is stated for arbitrary pairwise disjoint measurable sets `I j` of volume
  `ℓ j > 0` (rational intervals are the case `type_event_ge_Ico`), with `α j = n j / N` and the
  event `{v | ∀ j, #{i | v i ∈ I j} = n j}`; positivity of every `ℓ j` is needed (with `ℓ j = 0`
  and `n j > 0` the event is null while the right side, with Lean's `log 0 = 0`, is not).
* The template MGFs use natural exponents (the certificate multipliers are in `ℕ`), except the
  real-exponent versions for `-log U`, `U^p` and the log-ratio.
-/
import IIT.Census.ColSplit
import IIT.Census.Bernstein

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

/-! ### Exponential Markov for independent sums -/

section Generic

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- Markov with threshold one. -/
lemma measure_le_lintegral_of_one_le {S : Set Ω} {f : Ω → ENNReal} (hf : AEMeasurable f μ)
    (h : ∀ ω ∈ S, 1 ≤ f ω) : μ S ≤ ∫⁻ ω, f ω ∂μ :=
  calc μ S ≤ μ {ω | 1 ≤ f ω} := measure_mono h
    _ = 1 * μ {ω | 1 ≤ f ω} := (one_mul _).symm
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hf 1

/-- **Chernoff, lower tail** (`ENNReal` form): for independent `X i` and `t ≥ 0`,
`μ {∑ X i ≤ a} ≤ e^{t a} ∏ E e^{-t X i}`. -/
theorem chernoff_indep {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) {a t : ℝ} (ht : 0 ≤ t) :
    μ {ω | ∑ i ∈ s, X i ω ≤ a} ≤
      ENNReal.ofReal (Real.exp (t * a)) *
        ∏ i ∈ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * X i ω)) ∂μ := by
  have hm : ∀ i, Measurable fun ω => ENNReal.ofReal (Real.exp (-t * X i ω)) := fun i =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hmeas i).const_mul (-t)))
  have hind' : iIndepFun (fun i ω => ENNReal.ofReal (Real.exp (-t * X i ω))) μ :=
    hind.comp (fun _ x => ENNReal.ofReal (Real.exp (-t * x)))
      (fun _ => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _)))
  rw [← lintegral_prod_eq_prod_lintegral_of_indepFun s _ hind' hm,
    ← lintegral_const_mul _ (Finset.measurable_prod _ fun i _ => hm i)]
  refine measure_le_lintegral_of_one_le
    ((Finset.measurable_prod _ fun i _ => hm i).const_mul _).aemeasurable fun ω hω => ?_
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
  have hω' : ∑ i ∈ s, X i ω ≤ a := hω
  have : ∑ i ∈ s, -t * X i ω = -t * ∑ i ∈ s, X i ω := by rw [Finset.mul_sum]
  rw [this]
  nlinarith

/-- **Chernoff, upper tail** (`ENNReal` form). -/
theorem chernoff_indep_ge {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) {a t : ℝ} (ht : 0 ≤ t) :
    μ {ω | a ≤ ∑ i ∈ s, X i ω} ≤
      ENNReal.ofReal (Real.exp (-t * a)) *
        ∏ i ∈ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X i ω)) ∂μ := by
  have hind' : iIndepFun (fun i ω => -X i ω) μ :=
    hind.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have h := chernoff_indep (X := fun i ω => -X i ω) (a := -a) s hind' (fun i => (hmeas i).neg) ht
  have hset : {ω | a ≤ ∑ i ∈ s, X i ω} = {ω | ∑ i ∈ s, -X i ω ≤ -a} := by
    ext ω; simp [Finset.sum_neg_distrib]
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  · ring_nf
  · refine Finset.prod_congr rfl fun i _ => ?_
    congr 1; funext ω; ring_nf

/-- **Chernoff, lower tail**, real form (as stated in the blueprint). -/
theorem chernoff_indep_real [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} (s : Finset ι)
    (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i)) {a t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ i ∈ s, Integrable (fun ω => Real.exp (-t * X i ω)) μ) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ a} ≤
      Real.exp (t * a) * ∏ i ∈ s, ∫ ω, Real.exp (-t * X i ω) ∂μ := by
  have h := chernoff_indep s hind hmeas (a := a) ht
  have hI : ∀ i ∈ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * X i ω)) ∂μ =
      ENNReal.ofReal (∫ ω, Real.exp (-t * X i ω) ∂μ) := fun i hi =>
    (ofReal_integral_eq_lintegral_ofReal (hint i hi)
      (ae_of_all _ fun ω => (Real.exp_pos _).le)).symm
  rw [Finset.prod_congr rfl hI, ← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun ω => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h
  rw [measureReal_def]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal ?_)
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun i _ => integral_nonneg fun ω => (Real.exp_pos _).le)

end Generic

/-! ### Chernoff on a product measure -/

section Pi

variable {ι E : Type*} [Fintype ι] [MeasurableSpace E] (ν : ι → Measure E)
  [∀ i, IsProbabilityMeasure (ν i)]

/-- **Chernoff on `Measure.pi`**, lower tail of a sum of functions of the coordinates. -/
theorem chernoff_pi (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i)) {a t : ℝ} (ht : 0 ≤ t) :
    Measure.pi ν {x | ∑ i, f i (x i) ≤ a} ≤
      ENNReal.ofReal (Real.exp (t * a)) *
        ∏ i, ∫⁻ e, ENNReal.ofReal (Real.exp (-t * f i e)) ∂ν i := by
  have hind : iIndepFun (fun i (x : ι → E) => f i (x i)) (Measure.pi ν) :=
    iIndepFun_pi fun i => (hf i).aemeasurable
  refine (chernoff_indep (X := fun i (x : ι → E) => f i (x i)) univ hind
    (fun i => (hf i).comp (measurable_pi_apply i)) ht).trans_eq ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (measurePreserving_eval ν i).lintegral_comp
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hf i).const_mul (-t))))

/-- **Joint Chernoff on `Measure.pi`**: several linear constraints `∑ i f k i (x i) ≤ a k`
(`k ∈ K`) with multipliers `t k ≥ 0`, and a coordinatewise window `x i ∈ W i`. -/
theorem chernoff_pi_joint {κ : Type*} (K : Finset κ) (f : κ → ι → E → ℝ)
    (hf : ∀ k i, Measurable (f k i)) (a t : κ → ℝ) (ht : ∀ k ∈ K, 0 ≤ t k)
    (W : ι → Set E) (hW : ∀ i, MeasurableSet (W i)) :
    Measure.pi ν {x | (∀ i, x i ∈ W i) ∧ ∀ k ∈ K, ∑ i, f k i (x i) ≤ a k} ≤
      ENNReal.ofReal (Real.exp (∑ k ∈ K, t k * a k)) *
        ∏ i, ∫⁻ e in W i, ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i e)) ∂ν i := by
  set g : ι → E → ENNReal := fun i => (W i).indicator
    (fun e => ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i e))) with hg
  have hgm0 : ∀ i, Measurable fun e => ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i e)) :=
    fun i => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun k _ => (hf k i).const_mul (t k)).neg)
  have hgm : ∀ i, Measurable (g i) := fun i => (hgm0 i).indicator (hW i)
  have hind : iIndepFun (fun i (x : ι → E) => g i (x i)) (Measure.pi ν) :=
    iIndepFun_pi fun i => (hgm i).aemeasurable
  have hint : ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi ν = ∏ i, ∫⁻ e in W i,
      ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i e)) ∂ν i := by
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun univ _ hind
      (fun i => (hgm i).comp (measurable_pi_apply i))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(measurePreserving_eval ν i).lintegral_comp (hgm i), hg,
      lintegral_indicator (hW i)]
  have hGm : Measurable fun x : ι → E => ∏ i, g i (x i) :=
    Finset.measurable_prod _ fun i _ => (hgm i).comp (measurable_pi_apply i)
  rw [← hint, ← lintegral_const_mul _ hGm]
  refine measure_le_lintegral_of_one_le (hGm.const_mul _).aemeasurable fun x hx => ?_
  obtain ⟨hxW, hxK⟩ := hx
  have hgx : ∀ i, g i (x i) = ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i (x i))) :=
    fun i => by rw [hg]; exact Set.indicator_of_mem (hxW i) _
  simp_rw [hgx]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
  have e1 : ∑ i, -∑ k ∈ K, t k * f k i (x i) = -∑ k ∈ K, t k * ∑ i, f k i (x i) := by
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [e1, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun k hk => ?_
  rw [← mul_sub]
  exact mul_nonneg (ht k hk) (sub_nonneg.2 (hxK k hk))

end Pi

/-! ### The columns of the parameter cube -/

section Cols

variable {N : ℕ}

/-- The columns of a parameter vector: `colsOf w i r = w r i`. -/
def colsOf (w : Param N) : Fin N → State N → ℝ := fun i r => w r i

lemma measurable_colsOf : Measurable (colsOf (N := N)) :=
  Measurable.of_eval fun i => Measurable.of_eval fun r =>
    (measurable_pi_apply i).comp (measurable_pi_apply r)

/-- **The columns are iid with law `colLaw N`**: transposition carries `cubeM N` to the product
of the column laws. -/
theorem mp_colsOf :
    MeasurePreserving (colsOf (N := N)) (cubeM N) (Measure.pi fun _ : Fin N => colLaw N) := by
  have h4 : MeasurePreserving (MeasurableEquiv.curry (State N) (Fin N) ℝ)
      (Measure.pi fun _ => unif) (cubeM N) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : State N) (_ : Fin N) => unif)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  have h5 : MeasurePreserving (MeasurableEquiv.curry (Fin N) (State N) ℝ)
      (Measure.pi fun _ => unif) (Measure.pi fun _ : Fin N => colLaw N) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : Fin N) (_ : State N) => unif)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  have hsw : MeasurePreserving (fun (x : State N × Fin N → ℝ) (q : Fin N × State N) => x q.swap)
      (Measure.pi fun _ => unif) (Measure.pi fun _ => unif) :=
    ⟨Measurable.of_eval fun q => measurable_pi_apply _,
      map_comp_inj Prod.swap Prod.swap_injective unif⟩
  have h := (h5.comp hsw).comp (MeasurePreserving.symm _ h4)
  convert h using 1
  funext w i r
  rfl

/-- The law of one column. -/
lemma mp_colOf (i : Fin N) : MeasurePreserving (fun w : Param N => colsOf w i) (cubeM N) (colLaw N) :=
  (measurePreserving_eval (fun _ : Fin N => colLaw N) i).comp mp_colsOf

/-- **Column independence** under `cubeM N`. -/
theorem iIndepFun_cols : iIndepFun (fun (i : Fin N) (w : Param N) => colsOf w i) (cubeM N) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (mp_colOf i).measurable.aemeasurable]
  have h1 : (cubeM N).map (fun w i => colsOf w i) = Measure.pi fun _ : Fin N => colLaw N :=
    mp_colsOf.map_eq
  rw [h1]
  congr 1
  funext i
  exact (mp_colOf i).map_eq.symm

/-- **Chernoff over the columns** (one constraint). -/
theorem cubeM_chernoff_col_sum (F : Fin N → (State N → ℝ) → ℝ) (hF : ∀ i, Measurable (F i))
    {a t : ℝ} (ht : 0 ≤ t) :
    cubeM N {w | ∑ i, F i (fun r => w r i) ≤ a} ≤
      ENNReal.ofReal (Real.exp (t * a)) *
        ∏ i, ∫⁻ c, ENNReal.ofReal (Real.exp (-t * F i c)) ∂colLaw N := by
  have hpre : {w : Param N | ∑ i, F i (fun r => w r i) ≤ a} =
      colsOf ⁻¹' {x | ∑ i, F i (x i) ≤ a} := rfl
  rw [hpre]
  refine (Measure.le_map_apply measurable_colsOf.aemeasurable _).trans ?_
  rw [mp_colsOf.map_eq]
  exact chernoff_pi (fun _ => colLaw N) F hF ht

/-- **Joint Chernoff over the columns**: constraints `∑ i F k i (column i) ≤ a k` with
multipliers `t k ≥ 0` and a window on each column. -/
theorem cubeM_chernoff_cols {κ : Type*} (K : Finset κ) (F : κ → Fin N → (State N → ℝ) → ℝ)
    (hF : ∀ k i, Measurable (F k i)) (a t : κ → ℝ) (ht : ∀ k ∈ K, 0 ≤ t k)
    (W : Fin N → Set (State N → ℝ)) (hW : ∀ i, MeasurableSet (W i)) :
    cubeM N {w | (∀ i, (fun r => w r i) ∈ W i) ∧ ∀ k ∈ K, ∑ i, F k i (fun r => w r i) ≤ a k} ≤
      ENNReal.ofReal (Real.exp (∑ k ∈ K, t k * a k)) *
        ∏ i, ∫⁻ c in W i, ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * F k i c)) ∂colLaw N := by
  have hpre : {w : Param N | (∀ i, (fun r => w r i) ∈ W i) ∧
      ∀ k ∈ K, ∑ i, F k i (fun r => w r i) ≤ a k} =
      colsOf ⁻¹' {x | (∀ i, x i ∈ W i) ∧ ∀ k ∈ K, ∑ i, F k i (x i) ≤ a k} := rfl
  rw [hpre]
  refine (Measure.le_map_apply measurable_colsOf.aemeasurable _).trans ?_
  rw [mp_colsOf.map_eq]
  exact chernoff_pi_joint (fun _ => colLaw N) K F hF a t ht W hW

/-! #### Marginals of a column -/

lemma iIndepFun_colLaw :
    iIndepFun (fun (r : State N) (c : State N → ℝ) => c r) (colLaw N) :=
  iIndepFun_pi (X := fun _ x => x) fun _ => measurable_id.aemeasurable

lemma colLaw_map_eval (r : State N) : (colLaw N).map (fun c => c r) = unif :=
  (measurePreserving_eval (fun _ : State N => unif) r).map_eq

lemma colLaw_map_pair {r1 r2 : State N} (h : r1 ≠ r2) :
    (colLaw N).map (fun c => (c r1, c r2)) = unif.prod unif := by
  have := Measure.infinitePi_map_eval_prod (P := fun _ : State N => unif) h
  rwa [Measure.infinitePi_eq_pi] at this

lemma colLaw_map_triple {r1 r2 r3 : State N} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    (colLaw N).map (fun c => (c r1, c r2, c r3)) = unif.prod (unif.prod unif) := by
  have hind := (iIndepFun_colLaw.indepFun_prodMk (fun r => measurable_pi_apply r) r2 r3 r1
    h12.symm h13.symm).symm
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply r1).aemeasurable
    (by fun_prop), colLaw_map_eval, colLaw_map_pair h23]

/-- A function of two distinct entries of a column. -/
lemma lintegral_colLaw_pair {r1 r2 : State N} (h : r1 ≠ r2) {g : ℝ × ℝ → ENNReal}
    (hg : Measurable g) :
    ∫⁻ c, g (c r1, c r2) ∂colLaw N = ∫⁻ y, ∫⁻ u, g (y, u) ∂unif ∂unif := by
  have hpm : Measurable fun c : State N → ℝ => (c r1, c r2) := by fun_prop
  calc ∫⁻ c, g (c r1, c r2) ∂colLaw N
      = ∫⁻ p, g p ∂(colLaw N).map (fun c => (c r1, c r2)) := (lintegral_map hg hpm).symm
    _ = _ := by rw [colLaw_map_pair h, lintegral_prod _ hg.aemeasurable]

/-- A function of three distinct entries of a column. -/
lemma lintegral_colLaw_triple {r1 r2 r3 : State N} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) {g : ℝ × ℝ × ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ c, g (c r1, c r2, c r3) ∂colLaw N = ∫⁻ y, ∫⁻ u, ∫⁻ x, g (y, u, x) ∂unif ∂unif ∂unif := by
  have hpm : Measurable fun c : State N → ℝ => (c r1, c r2, c r3) := by fun_prop
  calc ∫⁻ c, g (c r1, c r2, c r3) ∂colLaw N
      = ∫⁻ p, g p ∂(colLaw N).map (fun c => (c r1, c r2, c r3)) := (lintegral_map hg hpm).symm
    _ = ∫⁻ y, ∫⁻ q, g (y, q) ∂(unif.prod unif) ∂unif := by
        rw [colLaw_map_triple h12 h13 h23, lintegral_prod _ hg.aemeasurable]
    _ = _ := by
        refine lintegral_congr fun y => ?_
        exact lintegral_prod (fun q => g (y, q)) (hg.comp measurable_prodMk_left).aemeasurable

/-- **Joint Chernoff for three rows**: per-column functions of the entries of three rows
`ra i, rb i, rc i` (distinct for each column `i`), with a window on the first entry. -/
theorem cubeM_chernoff_three {κ : Type*} (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (K : Finset κ) (f : κ → Fin N → ℝ × ℝ × ℝ → ℝ) (hf : ∀ k i, Measurable (f k i))
    (a t : κ → ℝ) (ht : ∀ k ∈ K, 0 ≤ t k) (W : Fin N → Set ℝ) (hW : ∀ i, MeasurableSet (W i)) :
    cubeM N {w | (∀ i, w (ra i) i ∈ W i) ∧
        ∀ k ∈ K, ∑ i, f k i (w (ra i) i, w (rb i) i, w (rc i) i) ≤ a k} ≤
      ENNReal.ofReal (Real.exp (∑ k ∈ K, t k * a k)) *
        ∏ i, ∫⁻ y in W i, ∫⁻ u, ∫⁻ x,
          ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i (y, u, x))) ∂unif ∂unif ∂unif := by
  have h := cubeM_chernoff_cols K (fun k i c => f k i (c (ra i), c (rb i), c (rc i)))
    (fun k i => (hf k i).comp (by fun_prop)) a t ht (fun i => {c | c (ra i) ∈ W i})
    (fun i => measurable_pi_apply (ra i) (hW i))
  refine h.trans_eq ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  set H : ℝ × ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i p)) with hH
  have hHm : Measurable H := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (Finset.measurable_sum _ fun k _ => (hf k i).const_mul (t k)).neg)
  have hWm : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ W i} := measurable_fst (hW i)
  have hWc : MeasurableSet {c : State N → ℝ | c (ra i) ∈ W i} :=
    measurable_pi_apply (ra i) (hW i)
  rw [← lintegral_indicator hWc]
  have e1 : ∀ c : State N → ℝ, ({c | c (ra i) ∈ W i} : Set (State N → ℝ)).indicator
      (fun c => H (c (ra i), c (rb i), c (rc i))) c =
      ({p : ℝ × ℝ × ℝ | p.1 ∈ W i}.indicator H) (c (ra i), c (rb i), c (rc i)) := fun c => by
    by_cases hc : c (ra i) ∈ W i
    · rw [Set.indicator_of_mem (show c ∈ {c | c (ra i) ∈ W i} from hc),
        Set.indicator_of_mem (show (c (ra i), c (rb i), c (rc i)) ∈ {p : ℝ × ℝ × ℝ | p.1 ∈ W i}
          from hc)]
    · rw [Set.indicator_of_notMem (show c ∉ {c | c (ra i) ∈ W i} from hc),
        Set.indicator_of_notMem (show (c (ra i), c (rb i), c (rc i)) ∉
          {p : ℝ × ℝ × ℝ | p.1 ∈ W i} from hc)]
  refine (lintegral_congr e1).trans ?_
  rw [lintegral_colLaw_triple (hab i) (hac i) (hbc i) (hHm.indicator hWm),
    ← lintegral_indicator (hW i)]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ W i
  · rw [Set.indicator_of_mem hy]
    refine lintegral_congr fun u => lintegral_congr fun x => ?_
    exact Set.indicator_of_mem (show (y, u, x) ∈ {p : ℝ × ℝ × ℝ | p.1 ∈ W i} from hy) _
  · rw [Set.indicator_of_notMem hy]
    calc _ = ∫⁻ _u : ℝ, ∫⁻ _x : ℝ, (0 : ENNReal) ∂unif ∂unif :=
          lintegral_congr fun u => lintegral_congr fun x =>
            Set.indicator_of_notMem (show (y, u, x) ∉ {p : ℝ × ℝ × ℝ | p.1 ∈ W i} from hy) _
      _ = 0 := by simp

end Cols

/-! ### The joint template of Section 3 -/

section Template

variable {N : ℕ}

/-- **The joint Chernoff template** (Section 3 of the B1 blueprint). Three rows per column: `ra i`
(the heavy row `tc`), `rb i` (the row entering the functional `g`) and `rc i` (the row `u`),
distinct in each column. A window `W` on the `tc` entries, the budget `∑ ℓ(tc) ≤ B`, the
row-`u` comparison `∑ ℓu(u) ≤ ∑ ℓ(tc)` and the functional `∑ g(tc, ·) ≤ 0`. For multipliers
`t, λu, λ ≥ 0`:
`P ≤ e^{t B} (∫_W e^{(λu - t) ℓ(y)} E_U[e^{-λ g(y,U)}] dy · E_x[e^{-λu ℓu(x)}])^N`. -/
theorem joint_template (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (ell ellU : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (hell : Measurable ell) (hellU : Measurable ellU)
    (hg : Measurable fun p : ℝ × ℝ => g p.1 p.2) (W : Set ℝ) (hW : MeasurableSet W)
    (B t lamU lam : ℝ) (ht : 0 ≤ t) (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) :
    cubeM N {w | (∀ i, w (ra i) i ∈ W) ∧ ∑ i, ell (w (ra i) i) ≤ B ∧
        ∑ i, ellU (w (rc i) i) ≤ ∑ i, ell (w (ra i) i) ∧ ∑ i, g (w (ra i) i) (w (rb i) i) ≤ 0} ≤
      ENNReal.ofReal (Real.exp (t * B)) *
        ((∫⁻ y in W, ENNReal.ofReal (Real.exp ((lamU - t) * ell y)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g y u)) ∂unif ∂unif) *
          ∫⁻ x, ENNReal.ofReal (Real.exp (-lamU * ellU x)) ∂unif) ^ N := by
  set f : Fin 3 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => ell p.1, fun _ p => ellU p.2.2 - ell p.1, fun _ p => g p.1 p.2.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp measurable_fst
    · exact (hellU.comp (measurable_snd.comp measurable_snd)).sub (hell.comp measurable_fst)
    · exact hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  set a : Fin 3 → ℝ := ![B, 0, 0] with ha
  set tt : Fin 3 → ℝ := ![t, lamU, lam] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 3)), 0 ≤ tt k := by
    intro k _; fin_cases k <;> simpa [htt]
  have hmain := cubeM_chernoff_three ra rb rc hab hac hbc univ f hfm a tt htt0 (fun _ => W)
    (fun _ => hW)
  refine (measure_mono ?_).trans (hmain.trans_eq ?_)
  · rintro w ⟨hW', hB, hU, hG⟩
    refine ⟨hW', fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hB
    · simp only [hf, ha, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Finset.sum_sub_distrib]; linarith
    · simpa [hf, ha] using hG
  · have hsum : ∑ k ∈ (univ : Finset (Fin 3)), tt k * a k = t * B := by
      simp [htt, ha, Fin.sum_univ_three]
    rw [hsum]
    congr 1
    have hexp : ∀ i y u x, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)),
        tt k * f k i (y, u, x))) = ENNReal.ofReal (Real.exp ((lamU - t) * ell y)) *
          ENNReal.ofReal (Real.exp (-lam * g y u)) *
            ENNReal.ofReal (Real.exp (-lamU * ellU x)) := by
      intro i y u x
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp only [Fin.sum_univ_three, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring
    have hA : Measurable fun y => ENNReal.ofReal (Real.exp ((lamU - t) * ell y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have hBm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-lam * g p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hg.const_mul _))
    have hC : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellU x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellU.const_mul _))
    have hIB : Measurable fun y => ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g y u)) ∂unif :=
      hBm.lintegral_prod_right'
    have hfac : ∀ i : Fin N, ∫⁻ y in W, ∫⁻ u, ∫⁻ x, ENNReal.ofReal (Real.exp
        (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i (y, u, x))) ∂unif ∂unif ∂unif =
        (∫⁻ y in W, ENNReal.ofReal (Real.exp ((lamU - t) * ell y)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g y u)) ∂unif ∂unif) *
          ∫⁻ x, ENNReal.ofReal (Real.exp (-lamU * ellU x)) ∂unif := by
      intro i
      have hAB : Measurable fun y => ENNReal.ofReal (Real.exp ((lamU - t) * ell y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g y u)) ∂unif := hA.mul hIB
      simp_rw [hexp i]
      rw [← lintegral_mul_const _ hAB]
      refine lintegral_congr fun y => ?_
      have hBy : Measurable fun u => ENNReal.ofReal (Real.exp (-lam * g y u)) :=
        hBm.comp (measurable_const.prodMk measurable_id)
      have hABy : Measurable fun u => ENNReal.ofReal (Real.exp ((lamU - t) * ell y)) *
          ENNReal.ofReal (Real.exp (-lam * g y u)) := hBy.const_mul _
      simp_rw [lintegral_const_mul _ hC]
      rw [lintegral_mul_const _ hABy, lintegral_const_mul _ hBy]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

end Template

/-! ### Closed-form moment generating functions under `unif` -/

section MGF

/-- `unif` is the Lebesgue measure on `(0, 1]`. -/
lemma unif_eq_Ioc : unif = volume.restrict (Set.Ioc (0 : ℝ) 1) :=
  (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm

lemma lintegral_unif_eq_Ioc (f : ℝ → ENNReal) :
    ∫⁻ u, f u ∂unif = ∫⁻ u in Set.Ioc (0 : ℝ) 1, f u := by
  rw [unif_eq_Ioc]

/-- `clamp01` is invisible under `unif`. -/
lemma lintegral_unif_clamp (f : ℝ → ENNReal) : ∫⁻ u, f (clamp01 u) ∂unif = ∫⁻ u, f u ∂unif := by
  unfold unif
  exact setLIntegral_congr_fun measurableSet_Icc fun u hu => by
    rw [clamp01_of_mem hu]

/-- A set integral over `(a, b]` of a nonnegative interval-integrable function. -/
lemma setLIntegral_Ioc_ofReal {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable h volume a b) (hpos : ∀ u ∈ Set.Ioc a b, 0 ≤ h u) :
    ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (h u) = ENNReal.ofReal (∫ u in a..b, h u) := by
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hint)
    (ae_restrict_of_forall_mem measurableSet_Ioc hpos)]

/-- `unif`-integrals of nonnegative interval-integrable functions. -/
lemma lintegral_unif_ofReal {h : ℝ → ℝ} (hint : IntervalIntegrable h volume 0 1)
    (hpos : ∀ u ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ h u) :
    ∫⁻ u, ENNReal.ofReal (h u) ∂unif = ENNReal.ofReal (∫ u in (0 : ℝ)..1, h u) := by
  rw [lintegral_unif_eq_Ioc, setLIntegral_Ioc_ofReal zero_le_one hint hpos]

/-- `e^{t · (-log x)} = x^{-t}`. -/
lemma exp_mul_neg_log {x : ℝ} (hx : 0 < x) (t : ℝ) : Real.exp (t * -Real.log x) = x ^ (-t) := by
  rw [Real.rpow_def_of_pos hx]; congr 1; ring

/-- `e^{-n log z} = (z⁻¹)^n`. -/
lemma exp_neg_nat_mul_log {z : ℝ} (hz : 0 < z) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log z) = z⁻¹ ^ n := by
  rw [show -(n : ℝ) * Real.log z = n * Real.log z⁻¹ by rw [Real.log_inv]; ring,
    Real.exp_nat_mul, Real.exp_log (inv_pos.2 hz)]

/-- `e^{-n · (-log x)} = x^n`. -/
lemma exp_neg_nat_mul_neg_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-(n : ℝ) * -Real.log x) = x ^ n := by
  rw [show -(n : ℝ) * -Real.log x = n * Real.log x by ring, Real.exp_nat_mul, Real.exp_log hx]

/-- **MGF of `-log U`**: `E e^{t(-log U)} = 1/(1-t)` for `t < 1` (in particular
`E e^{-λ(-log U)} = E U^λ = 1/(1+λ)`). -/
theorem lintegral_unif_negLog {t : ℝ} (ht : t < 1) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (t * -Real.log (clamp01 u))) ∂unif =
      ENNReal.ofReal (1 / (1 - t)) := by
  rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (Real.exp (t * -Real.log u))),
    lintegral_unif_eq_Ioc, setLIntegral_congr_fun measurableSet_Ioc
      (g := fun u => ENNReal.ofReal (u ^ (-t))) fun u hu => by
        rw [exp_mul_neg_log hu.1],
    setLIntegral_Ioc_ofReal zero_le_one (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      fun u hu => Real.rpow_nonneg hu.1.le _,
    integral_rpow (Or.inl (by linarith))]
  congr 1
  rw [Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- **Moments of `U`** (real exponent): `E U^p = 1/(p+1)` for `p > -1`. -/
theorem lintegral_unif_rpow {p : ℝ} (hp : -1 < p) :
    ∫⁻ u, ENNReal.ofReal (clamp01 u ^ p) ∂unif = ENNReal.ofReal (1 / (p + 1)) := by
  rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (u ^ p)),
    lintegral_unif_ofReal (intervalIntegral.intervalIntegrable_rpow' hp)
      fun u hu => Real.rpow_nonneg hu.1.le _,
    integral_rpow (Or.inl hp)]
  congr 1
  rw [Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- **Moments of `U`**: `E U^n = 1/(n+1)`. -/
theorem lintegral_unif_pow (n : ℕ) :
    ∫⁻ u, ENNReal.ofReal (clamp01 u ^ n) ∂unif = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (u ^ n)),
    lintegral_unif_ofReal ((continuous_pow n).intervalIntegrable 0 1)
      fun u hu => pow_nonneg hu.1.le _, integral_pow]
  congr 1
  simp

/-- `∫_a^b ((y+u)/(2y))^n du`. -/
lemma integral_logRatio_pow {y : ℝ} (hy : 0 < y) (n : ℕ) (a b : ℝ) :
    ∫ u in a..b, ((y + u) / (2 * y)) ^ n =
      ((y + b) ^ (n + 1) - (y + a) ^ (n + 1)) / (((n : ℝ) + 1) * (2 * y) ^ n) := by
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div]
  have h2 : ∫ u in a..b, (y + u) ^ n = ((y + b) ^ (n + 1) - (y + a) ^ (n + 1)) / ((n : ℝ) + 1) := by
    have := intervalIntegral.integral_comp_add_right (fun x => x ^ n) y (a := a) (b := b)
    rw [show (fun u => (y + u) ^ n) = fun u => (u + y) ^ n by funext u; ring_nf, this,
      integral_pow, add_comm a y, add_comm b y]
  rw [h2]
  have : (0 : ℝ) < (2 * y) ^ n := by positivity
  field_simp

/-- **MGF of the log-ratio** `V = log (2y/(y+U))`: for `y > 0`,
`E e^{-n V} = E ((y+U)/(2y))^n = ((1+y)^{n+1} - y^{n+1}) / ((n+1)(2y)^n)`. -/
theorem lintegral_unif_logRatio {y : ℝ} (hy : 0 < y) (n : ℕ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log (2 * y / (y + clamp01 u)))) ∂unif =
      ENNReal.ofReal (((1 + y) ^ (n + 1) - y ^ (n + 1)) / (((n : ℝ) + 1) * (2 * y) ^ n)) := by
  rw [lintegral_unif_clamp
      (fun u => ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log (2 * y / (y + u))))),
    lintegral_unif_eq_Ioc, setLIntegral_congr_fun measurableSet_Ioc
      (g := fun u => ENNReal.ofReal (((y + u) / (2 * y)) ^ n)) fun u hu => by
        rw [exp_neg_nat_mul_log (by have := hu.1; positivity), inv_div],
    setLIntegral_Ioc_ofReal zero_le_one
      ((show Continuous fun u : ℝ => ((y + u) / (2 * y)) ^ n by fun_prop).intervalIntegrable 0 1)
      fun u hu => pow_nonneg (div_nonneg (by linarith [hu.1]) (by linarith)) _,
    integral_logRatio_pow hy n 0 1]
  congr 1
  ring_nf

/-- **MGF of the log-ratio**, real exponent: for `y > 0` and `λ > -1`,
`E ((y+U)/(2y))^λ = ((1+y)^{λ+1} - y^{λ+1}) / ((λ+1)(2y)^λ)`. -/
theorem lintegral_unif_logRatio_rpow {y : ℝ} (hy : 0 < y) {lam : ℝ} (hlam : -1 < lam) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * Real.log (2 * y / (y + clamp01 u)))) ∂unif =
      ENNReal.ofReal (((1 + y) ^ (lam + 1) - y ^ (lam + 1)) / ((lam + 1) * (2 * y) ^ lam)) := by
  have hpt : ∀ u, 0 ≤ u → Real.exp (-lam * Real.log (2 * y / (y + u))) =
      (u + y) ^ lam / (2 * y) ^ lam := by
    intro u hu
    have hyu : 0 < y + u := by linarith
    rw [← Real.div_rpow (by linarith) (by linarith), Real.rpow_def_of_pos (by positivity),
      show (u + y) / (2 * y) = (2 * y / (y + u))⁻¹ by rw [inv_div, add_comm], Real.log_inv]
    congr 1; ring
  rw [lintegral_unif_clamp
      (fun u => ENNReal.ofReal (Real.exp (-lam * Real.log (2 * y / (y + u))))),
    lintegral_unif_eq_Ioc, setLIntegral_congr_fun measurableSet_Ioc
      (g := fun u => ENNReal.ofReal ((u + y) ^ lam / (2 * y) ^ lam)) fun u hu => by
        rw [hpt u hu.1.le]]
  have hint : IntervalIntegrable (fun u => (u + y) ^ lam / (2 * y) ^ lam) volume 0 1 := by
    have h1 : IntervalIntegrable (fun u => u ^ lam) volume (0 + y) (1 + y) :=
      intervalIntegral.intervalIntegrable_rpow' hlam
    have h3 := h1.comp_add_right y
    rw [show (0 : ℝ) + y - y = 0 by ring, show (1 : ℝ) + y - y = 1 by ring] at h3
    exact h3.div_const _
  rw [setLIntegral_Ioc_ofReal zero_le_one hint
      fun u hu => div_nonneg (Real.rpow_nonneg (by linarith [hu.1]) _)
        (Real.rpow_nonneg (by linarith) _),
    intervalIntegral.integral_div, intervalIntegral.integral_comp_add_right (fun x => x ^ lam) y,
    integral_rpow (Or.inl hlam), zero_add]
  congr 1
  rw [div_div]

/-- **MGF of the truncated log-ratio** `V = min (log (2y/(y+U))) (log (y/c))`: when
`0 ≤ 2c - y ≤ 1`, `E e^{-n V} = (2c - y)(c/y)^n + ((1+y)^{n+1} - (2c)^{n+1}) / ((n+1)(2y)^n)`. -/
theorem lintegral_unif_logRatioTrunc {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (h1 : y ≤ 2 * c)
    (h2 : 2 * c ≤ y + 1) (n : ℕ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(n : ℝ) *
        min (Real.log (2 * y / (y + clamp01 u))) (Real.log (y / c)))) ∂unif =
      ENNReal.ofReal ((2 * c - y) * (c / y) ^ n +
        ((1 + y) ^ (n + 1) - (2 * c) ^ (n + 1)) / (((n : ℝ) + 1) * (2 * y) ^ n)) := by
  set d := 2 * c - y with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hd1 : d ≤ 1 := by rw [hd]; linarith
  rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (Real.exp (-(n : ℝ) *
      min (Real.log (2 * y / (y + u))) (Real.log (y / c))))), lintegral_unif_eq_Ioc,
    ← Set.Ioc_union_Ioc_eq_Ioc hd0 hd1,
    lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc.2 (by simp))]
  have hA : ∫⁻ u in Set.Ioc 0 d, ENNReal.ofReal (Real.exp (-(n : ℝ) *
      min (Real.log (2 * y / (y + u))) (Real.log (y / c)))) =
      ENNReal.ofReal (d * (c / y) ^ n) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => ENNReal.ofReal ((c / y) ^ n))
      fun u hu => ?_]
    · rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
        mul_comm]
    · have hyu : 0 < y + u := by linarith [hu.1]
      have hle : Real.log (y / c) ≤ Real.log (2 * y / (y + u)) := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ hc hyu]
        nlinarith [hu.2]
      rw [min_eq_right hle, exp_neg_nat_mul_log (by positivity), inv_div]
  have hB : ∫⁻ u in Set.Ioc d 1, ENNReal.ofReal (Real.exp (-(n : ℝ) *
      min (Real.log (2 * y / (y + u))) (Real.log (y / c)))) =
      ENNReal.ofReal (((1 + y) ^ (n + 1) - (2 * c) ^ (n + 1)) / (((n : ℝ) + 1) * (2 * y) ^ n)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun u => ENNReal.ofReal (((y + u) / (2 * y)) ^ n)) fun u hu => ?_]
    · rw [setLIntegral_Ioc_ofReal hd1
        ((show Continuous fun u : ℝ => ((y + u) / (2 * y)) ^ n by fun_prop).intervalIntegrable d 1)
        fun u hu => pow_nonneg (div_nonneg (by linarith [hu.1]) (by linarith)) _,
        integral_logRatio_pow hy n d 1, hd]
      congr 2
      ring
    · have hyu : 0 < y + u := by linarith [hu.1]
      have hle : Real.log (2 * y / (y + u)) ≤ Real.log (y / c) := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ hyu hc]
        nlinarith [hu.1]
      rw [min_eq_left hle, exp_neg_nat_mul_log (by positivity), inv_div]
  rw [hA, hB, ← ENNReal.ofReal_add (by positivity)]
  have : (2 * c) ^ (n + 1) ≤ (1 + y) ^ (n + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
  exact div_nonneg (by linarith) (by positivity)

/-- **Moments of the folded variable** `max U (1-U)` (uniform on `[1/2, 1]`):
`E max(U,1-U)^n = 2 (1 - (1/2)^{n+1}) / (n+1)`. -/
theorem lintegral_unif_fold_pow (n : ℕ) :
    ∫⁻ u, ENNReal.ofReal (max (clamp01 u) (1 - clamp01 u) ^ n) ∂unif =
      ENNReal.ofReal (2 * (1 - (1 / 2 : ℝ) ^ (n + 1)) / ((n : ℝ) + 1)) := by
  have hc : Continuous fun u : ℝ => max u (1 - u) ^ n :=
    (continuous_id.max (continuous_const.sub continuous_id)).pow n
  rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (max u (1 - u) ^ n)),
    lintegral_unif_ofReal (hc.intervalIntegrable 0 1)
      fun u hu => pow_nonneg ((le_max_left _ _).trans' hu.1.le) _,
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 / 2))
      (hc.intervalIntegrable (1 / 2) 1)]
  have e1 : ∫ u in (0 : ℝ)..1 / 2, max u (1 - u) ^ n = ∫ u in (1 / 2 : ℝ)..1, u ^ n := by
    rw [intervalIntegral.integral_congr (g := fun u => (1 - u) ^ n) fun u hu => ?_]
    · have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) (1 : ℝ)
        (a := 0) (b := 1 / 2)
      rw [this]; norm_num
    · rw [Set.uIcc_of_le (by norm_num)] at hu
      rw [max_eq_right (by linarith [hu.2])]
  have e2 : ∫ u in (1 / 2 : ℝ)..1, max u (1 - u) ^ n = ∫ u in (1 / 2 : ℝ)..1, u ^ n := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hu
    rw [max_eq_left (by linarith [hu.1])]
  rw [e1, e2, integral_pow]
  congr 1
  simp only [one_pow]
  ring

/-- `e^{-n (-log max(U,1-U))} = max(U,1-U)^n` (the row-`u` factor of the template). -/
lemma exp_neg_nat_mul_neg_log_fold (u : ℝ) (n : ℕ) :
    Real.exp (-(n : ℝ) * -Real.log (max (clamp01 u) (1 - clamp01 u))) =
      max (clamp01 u) (1 - clamp01 u) ^ n := by
  refine exp_neg_nat_mul_neg_log ?_ n
  rcases le_total (clamp01 u) (1 / 2) with h | h
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)

/-- **MGF of `U`**: `E e^{tU} = (e^t - 1)/t` for `t ≠ 0`. -/
theorem lintegral_unif_exp {t : ℝ} (ht : t ≠ 0) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (t * clamp01 u)) ∂unif =
      ENNReal.ofReal ((Real.exp t - 1) / t) := by
  rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (Real.exp (t * u))),
    lintegral_unif_ofReal
      ((show Continuous fun u : ℝ => Real.exp (t * u) by fun_prop).intervalIntegrable 0 1)
      fun u _ => (Real.exp_pos _).le,
    intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) ht, integral_exp]
  congr 1
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul]
  ring

end MGF

/-! ### Cramér lower tail of `∑ -log U` -/

section Gamma

variable {N : ℕ}

lemma measurable_negLogClamp : Measurable fun u : ℝ => -Real.log (clamp01 u) :=
  (Real.measurable_log.comp clamp01_measurable).neg

/-- **Chernoff for `∑_{i ∈ M} -log U_i`** at any `t ≥ 0`: `P(∑ ≤ x) ≤ e^{t x} (1+t)^{-|M|}`. -/
theorem rowM_negLog_chernoff (M : Finset (Fin N)) {x t : ℝ} (ht : 0 ≤ t) :
    rowM N {v | ∑ i ∈ M, -Real.log (clamp01 (v i)) ≤ x} ≤
      ENNReal.ofReal (Real.exp (t * x) * (1 / (1 + t)) ^ M.card) := by
  have hind : iIndepFun (fun i (v : Fin N → ℝ) => -Real.log (clamp01 (v i))) (rowM N) := by
    unfold rowM
    exact iIndepFun_pi (X := fun _ u => -Real.log (clamp01 u))
      fun _ => measurable_negLogClamp.aemeasurable
  refine (chernoff_indep M hind (fun i => measurable_negLogClamp.comp (measurable_pi_apply i))
    ht).trans_eq ?_
  have h1 : ∀ i, ∫⁻ v, ENNReal.ofReal (Real.exp (-t * -Real.log (clamp01 (v i)))) ∂rowM N =
      ENNReal.ofReal (1 / (1 + t)) := fun i => by
    have := lintegral_unif_negLog (t := -t) (by linarith)
    rw [show (1 : ℝ) - -t = 1 + t by ring] at this
    rw [← this]
    exact (measurePreserving_eval (fun _ : Fin N => unif) i).lintegral_comp
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_negLogClamp.const_mul _)))
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_const,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **Cramér lower tail of `∑_{i ∈ M} -log U_i`** (`m = |M|`, `0 < x ≤ m`):
`P(∑ ≤ x) ≤ exp (-m (x/m - 1 - log (x/m)))`. -/
theorem rowM_negLog_sum_le (M : Finset (Fin N)) {x : ℝ} (hx : 0 < x) (hxM : x ≤ M.card) :
    rowM N {v | ∑ i ∈ M, -Real.log (clamp01 (v i)) ≤ x} ≤
      ENNReal.ofReal (Real.exp (-(M.card * (x / M.card - 1 - Real.log (x / M.card))))) := by
  have hm : (0 : ℝ) < M.card := hx.trans_le hxM
  have ht : 0 ≤ (M.card : ℝ) / x - 1 := by rw [sub_nonneg, le_div_iff₀ hx]; linarith
  refine (rowM_negLog_chernoff M ht).trans_eq ?_
  congr 1
  have hxm : 0 < x / M.card := div_pos hx hm
  rw [show 1 + ((M.card : ℝ) / x - 1) = M.card / x by ring, one_div_div,
    ← Real.exp_log hxm, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_log hxm]
  congr 1
  field_simp
  ring

/-- **Gamma lower tail** (volume form): for `0 < x ≤ n`,
`volume {v ∈ [0,1]^n | e^{-x} ≤ ∏ v} ≤ exp (-n (x/n - 1 - log (x/n)))`. -/
theorem gamma_lower_tail (n : ℕ) {x : ℝ} (hx : 0 < x) (hxn : x ≤ n) :
    volume {v : Fin n → ℝ | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧ Real.exp (-x) ≤ ∏ i, v i} ≤
      ENNReal.ofReal (Real.exp (-(n * (x / n - 1 - Real.log (x / n))))) := by
  have hsub : {v : Fin n → ℝ | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧ Real.exp (-x) ≤ ∏ i, v i} ⊆
      {v | ∑ i ∈ (univ : Finset (Fin n)), -Real.log (clamp01 (v i)) ≤ x} ∩ cubeRow n := by
    rintro v ⟨hv, hp⟩
    refine ⟨?_, fun i _ => hv i⟩
    have hpos : ∀ i, v i ≠ 0 := by
      intro i hi
      have : ∏ j, v j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      linarith [Real.exp_pos (-x)]
    show ∑ i, -Real.log (clamp01 (v i)) ≤ x
    rw [Finset.sum_congr rfl fun i _ => by rw [clamp01_of_mem (hv i)], Finset.sum_neg_distrib,
      ← Real.log_prod fun i _ => hpos i]
    have := Real.log_le_log (Real.exp_pos _) hp
    rw [Real.log_exp] at this
    linarith
  have h := rowM_negLog_sum_le (N := n) univ hx (by simpa using hxn)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  calc volume {v : Fin n → ℝ | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧ Real.exp (-x) ≤ ∏ i, v i}
      ≤ volume ({v | ∑ i ∈ (univ : Finset (Fin n)), -Real.log (clamp01 (v i)) ≤ x} ∩ cubeRow n) :=
        measure_mono hsub
    _ = rowM n {v | ∑ i ∈ (univ : Finset (Fin n)), -Real.log (clamp01 (v i)) ≤ x} := by
        rw [← restrict_row, Measure.restrict_apply' measurableSet_cubeRow]
    _ ≤ _ := h

/-- **Several independent rows** (product of row laws over any finite index `R`, e.g. the fresh
rows of the resampling): some row has `∑_{i ∈ M} -log ≤ x` with probability at most
`|R| exp (-m (x/m - 1 - log (x/m)))`. -/
theorem pi_rows_negLog_tail {R : Type*} [Fintype R] (M : Finset (Fin N)) {x : ℝ} (hx : 0 < x)
    (hxM : x ≤ M.card) :
    (Measure.pi fun _ : R => rowM N) {V | ∃ r, ∑ i ∈ M, -Real.log (clamp01 (V r i)) ≤ x} ≤
      ENNReal.ofReal (Fintype.card R *
        Real.exp (-(M.card * (x / M.card - 1 - Real.log (x / M.card))))) := by
  have hU : {V : R → Fin N → ℝ | ∃ r, ∑ i ∈ M, -Real.log (clamp01 (V r i)) ≤ x} =
      ⋃ r, (fun V : R → Fin N → ℝ => V r) ⁻¹' {v | ∑ i ∈ M, -Real.log (clamp01 (v i)) ≤ x} := by
    ext V; simp
  rw [hU]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc ∑ r, (Measure.pi fun _ : R => rowM N) ((fun V : R → Fin N → ℝ => V r) ⁻¹'
        {v | ∑ i ∈ M, -Real.log (clamp01 (v i)) ≤ x})
      ≤ ∑ _r : R, ENNReal.ofReal
          (Real.exp (-(M.card * (x / M.card - 1 - Real.log (x / M.card))))) := by
        refine Finset.sum_le_sum fun r _ => ?_
        refine (Measure.le_map_apply (measurable_pi_apply r).aemeasurable _).trans ?_
        rw [(measurePreserving_eval (fun _ : R => rowM N) r).map_eq]
        exact rowM_negLog_sum_le M hx hxM
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- **A finite set of rows of the cube**: some row `r ∈ A` has `∑_{i ∈ M} -log ≤ x` with
probability at most `|A| exp (-m (x/m - 1 - log (x/m)))`. -/
theorem cubeM_rows_negLog_tail (A : Finset (State N)) (M : Finset (Fin N)) {x : ℝ} (hx : 0 < x)
    (hxM : x ≤ M.card) :
    cubeM N {w | ∃ r ∈ A, ∑ i ∈ M, -Real.log (clamp01 (w r i)) ≤ x} ≤
      ENNReal.ofReal (A.card * Real.exp (-(M.card * (x / M.card - 1 - Real.log (x / M.card))))) := by
  have hU : {w : Param N | ∃ r ∈ A, ∑ i ∈ M, -Real.log (clamp01 (w r i)) ≤ x} =
      ⋃ r ∈ A, (fun w : Param N => w r) ⁻¹' {v | ∑ i ∈ M, -Real.log (clamp01 (v i)) ≤ x} := by
    ext w; simp
  rw [hU]
  refine (measure_biUnion_finset_le A _).trans ?_
  calc ∑ r ∈ A, cubeM N ((fun w : Param N => w r) ⁻¹'
        {v | ∑ i ∈ M, -Real.log (clamp01 (v i)) ≤ x})
      ≤ ∑ _r ∈ A, ENNReal.ofReal
          (Real.exp (-(M.card * (x / M.card - 1 - Real.log (x / M.card))))) := by
        refine Finset.sum_le_sum fun r _ => ?_
        refine (Measure.le_map_apply (measurable_pi_apply r).aemeasurable _).trans ?_
        have hmp := measurePreserving_eval (fun _ : State N => rowM N) r
        unfold cubeM
        rw [hmp.map_eq]
        exact rowM_negLog_sum_le M hx hxM
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- **`min_rows_tail`** (blueprint A4): some row outside `A` has `XW w r ≤ x`
(`XW w r = ∑ i, -log (clamp01 (w r i))`) with probability at most
`2^N exp (-N (x/N - 1 - log (x/N)))`, for `0 < x ≤ N`. -/
theorem min_rows_tail (A : Finset (State N)) {x : ℝ} (hx : 0 < x) (hxN : x ≤ N) :
    cubeM N {w | ∃ r ∉ A, ∑ i, -Real.log (clamp01 (w r i)) ≤ x} ≤
      ENNReal.ofReal (2 ^ N * Real.exp (-(N * (x / N - 1 - Real.log (x / N))))) := by
  have h := cubeM_rows_negLog_tail (univ \ A) univ hx (by simpa using hxN)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  refine (measure_mono ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · rintro w ⟨r, hr, hw⟩
    exact ⟨r, by simpa using hr, hw⟩
  · refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have : (univ \ A).card ≤ 2 ^ N := (Finset.card_le_univ _).trans_eq (by simp)
    exact_mod_cast this

end Gamma

/-! ### The multinomial ("type") lower bound -/

section TypeEvent

open Nat in
/-- `a^b a! ≤ a^a b!` (the Poisson weight `a^b/b!` is maximal at `b = a`). -/
lemma pow_mul_factorial_le (a b : ℕ) : a ^ b * a ! ≤ a ^ a * b ! := by
  rcases le_total b a with hba | hab
  · have h1 : b ! * a.descFactorial (a - b) = a ! := by
      have := Nat.factorial_mul_descFactorial (n := a) (k := a - b) (Nat.sub_le a b)
      rwa [Nat.sub_sub_self hba] at this
    have h2 : a ^ b * a ^ (a - b) = a ^ a := by rw [← pow_add, Nat.add_sub_cancel' hba]
    calc a ^ b * a ! = a ^ b * b ! * a.descFactorial (a - b) := by rw [← h1]; ring
      _ ≤ a ^ b * b ! * a ^ (a - b) := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
      _ = a ^ a * b ! := by rw [← h2]; ring
  · have h1 : a ! * (a + 1) ^ (b - a) ≤ b ! := by
      have := Nat.factorial_mul_pow_le_factorial (m := a) (n := b - a)
      rwa [Nat.add_sub_cancel' hab] at this
    have h2 : a ^ a * a ^ (b - a) = a ^ b := by rw [← pow_add, Nat.add_sub_cancel' hab]
    calc a ^ b * a ! = a ^ a * (a ! * a ^ (b - a)) := by rw [← h2]; ring
      _ ≤ a ^ a * (a ! * (a + 1) ^ (b - a)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ a) _))
      _ ≤ a ^ a * b ! := Nat.mul_le_mul_left _ h1

/-- The type of an assignment `σ : Fin N → Fin k`: the sizes of its fibres. -/
def fibType {N k : ℕ} (σ : Fin N → Fin k) (j : Fin k) : ℕ := (univ.filter fun i => σ i = j).card

lemma sum_fibType {N k : ℕ} (σ : Fin N → Fin k) : ∑ j, fibType σ j = N := by
  unfold fibType
  rw [← Finset.card_eq_sum_card_fiberwise (f := σ) (s := univ) (t := univ)
    (fun _ _ => Finset.mem_coe.2 (mem_univ _))]
  simp

lemma fibType_le {N k : ℕ} (σ : Fin N → Fin k) (j : Fin k) : fibType σ j ≤ N :=
  (card_filter_le _ _).trans (by simp)

lemma fibType_cons {N k : ℕ} (a : Fin k) (τ : Fin N → Fin k) (j : Fin k) :
    fibType (Fin.cons a τ : Fin (N + 1) → Fin k) j = fibType τ j + if a = j then 1 else 0 := by
  unfold fibType
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- The number of assignments of type `m`. -/
def fibTypeCount (N k : ℕ) (m : Fin k → ℕ) : ℕ :=
  (univ.filter fun σ : Fin N → Fin k => fibType σ = m).card

lemma fibType_cons_eq_iff {N k : ℕ} (a : Fin k) (τ : Fin N → Fin k) (m : Fin k → ℕ) :
    fibType (Fin.cons a τ : Fin (N + 1) → Fin k) = m ↔
      1 ≤ m a ∧ fibType τ = Function.update m a (m a - 1) := by
  constructor
  · intro h
    have ha := congrFun h a
    rw [fibType_cons, ite_eq_left rfl] at ha
    refine ⟨by omega, funext fun j => ?_⟩
    by_cases hj : j = a
    · subst hj; rw [Function.update_self]; omega
    · have := congrFun h j
      rw [fibType_cons, ite_eq_right (Ne.symm hj), add_zero] at this
      rw [Function.update_of_ne hj, this]
  · rintro ⟨h1, h2⟩
    funext j
    rw [fibType_cons, h2]
    by_cases hj : j = a
    · subst hj; rw [Function.update_self, ite_eq_left rfl]; omega
    · rw [Function.update_of_ne hj, ite_eq_right (Ne.symm hj), add_zero]

lemma fibTypeCount_succ {N k : ℕ} (m : Fin k → ℕ) :
    fibTypeCount (N + 1) k m = ∑ a : Fin k,
      if 1 ≤ m a then fibTypeCount N k (Function.update m a (m a - 1)) else 0 := by
  unfold fibTypeCount
  rw [Finset.card_filter, ← (Fin.consEquiv fun _ : Fin (N + 1) => Fin k).sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  change (∑ τ : Fin N → Fin k,
    if fibType (Fin.cons a τ : Fin (N + 1) → Fin k) = m then 1 else 0) = _
  simp_rw [fibType_cons_eq_iff]
  split_ifs with h
  · rw [Finset.card_filter]
    simp [h]
  · simp [h]

/-- **Multinomial count**: the number of assignments of type `m` is `N! / ∏ m j!`. -/
theorem fibTypeCount_mul_prod_factorial {k : ℕ} :
    ∀ (N : ℕ) (m : Fin k → ℕ), ∑ j, m j = N → fibTypeCount N k m * ∏ j, (m j).factorial = N.factorial
  | 0, m, hm => by
    have hm0 : m = 0 := funext fun j => by
      have := (Finset.sum_eq_zero_iff.1 hm) j (mem_univ j); simpa using this
    subst hm0
    have : fibTypeCount 0 k 0 = 1 := by
      unfold fibTypeCount
      rw [Finset.filter_true_of_mem fun σ _ => funext fun j => by simp [fibType]]
      simp
    simp [this]
  | N + 1, m, hm => by
    rw [fibTypeCount_succ, Finset.sum_mul]
    have hterm : ∀ a : Fin k, (if 1 ≤ m a then fibTypeCount N k (Function.update m a (m a - 1))
        else 0) * ∏ j, (m j).factorial = m a * N.factorial := by
      intro a
      split_ifs with ha
      · have hsum : ∑ j, Function.update m a (m a - 1) j = N := by
          rw [Finset.sum_update_of_mem (mem_univ a)]
          have := Finset.add_sum_erase univ m (mem_univ a)
          rw [Finset.sdiff_singleton_eq_erase]
          omega
        have hIH := fibTypeCount_mul_prod_factorial N _ hsum
        have hprod : ∏ j, (m j).factorial =
            m a * ∏ j, (Function.update m a (m a - 1) j).factorial := by
          rw [← Finset.mul_prod_erase univ _ (mem_univ a),
            ← Finset.mul_prod_erase univ (fun j => (Function.update m a (m a - 1) j).factorial)
              (mem_univ a), Function.update_self, ← mul_assoc,
            Nat.mul_factorial_pred (by omega)]
          congr 1
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        rw [hprod, ← hIH]
        ring
      · have : m a = 0 := by omega
        rw [this]; simp
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_mul, hm, Nat.factorial_succ]

/-- **The type class is the largest**: `N^N ≤ (N+1)^k · #T(n) · ∏ n_j^{n_j}`. -/
theorem pow_le_fibTypeCount {k N : ℕ} (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    N ^ N ≤ (N + 1) ^ k * (fibTypeCount N k n * ∏ j, n j ^ n j) := by
  set w : (Fin k → ℕ) → ℕ := fun m => ∏ j, n j ^ m j with hw
  have h1 : N ^ N = ∑ σ : Fin N → Fin k, w (fibType σ) := by
    have e1 : N ^ N = ∏ _i : Fin N, ∑ j, n j := by
      rw [Finset.prod_const, hn, Finset.card_univ, Fintype.card_fin]
    rw [e1, Fintype.prod_sum (fun (_ : Fin N) (j : Fin k) => n j)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hw, ← Finset.prod_fiberwise univ σ (fun i => n (σ i))]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
    rfl
  have hbound : ∀ m ∈ (univ : Finset (Fin N → Fin k)).image fibType,
      fibTypeCount N k m * w m ≤ fibTypeCount N k n * w n := by
    intro m hm
    obtain ⟨σ0, _, rfl⟩ := Finset.mem_image.1 hm
    have hA := fibTypeCount_mul_prod_factorial N (fibType σ0) (sum_fibType σ0)
    have hB := fibTypeCount_mul_prod_factorial N n hn
    have hP : 0 < (∏ j, (fibType σ0 j).factorial) * ∏ j, (n j).factorial :=
      Nat.mul_pos (Finset.prod_pos fun j _ => Nat.factorial_pos _)
        (Finset.prod_pos fun j _ => Nat.factorial_pos _)
    refine Nat.le_of_mul_le_mul_right ?_ hP
    have hj : ∏ j, (n j ^ fibType σ0 j * (n j).factorial) ≤
        ∏ j, (n j ^ n j * (fibType σ0 j).factorial) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        fun j _ => pow_mul_factorial_le (n j) (fibType σ0 j)
    calc fibTypeCount N k (fibType σ0) * w (fibType σ0) *
          ((∏ j, (fibType σ0 j).factorial) * ∏ j, (n j).factorial)
        = (fibTypeCount N k (fibType σ0) * ∏ j, (fibType σ0 j).factorial) *
            ∏ j, (n j ^ fibType σ0 j * (n j).factorial) := by
          rw [hw, Finset.prod_mul_distrib]; ring
      _ ≤ (fibTypeCount N k n * ∏ j, (n j).factorial) *
            ∏ j, (n j ^ n j * (fibType σ0 j).factorial) := by
          rw [hA, hB]; exact Nat.mul_le_mul_left _ hj
      _ = fibTypeCount N k n * w n * ((∏ j, (fibType σ0 j).factorial) * ∏ j, (n j).factorial) := by
          rw [hw, Finset.prod_mul_distrib]; ring
  have himage : ((univ : Finset (Fin N → Fin k)).image fibType).card ≤ (N + 1) ^ k := by
    have hsub : (univ : Finset (Fin N → Fin k)).image fibType ⊆
        Fintype.piFinset fun _ : Fin k => Finset.range (N + 1) := by
      intro m hm
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.1 hm
      exact Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 (Nat.lt_succ_of_le (fibType_le σ j))
    refine (Finset.card_le_card hsub).trans_eq ?_
    rw [Fintype.card_piFinset]
    simp
  rw [h1, Finset.sum_comp]
  calc ∑ m ∈ (univ : Finset (Fin N → Fin k)).image fibType,
        (univ.filter fun σ : Fin N → Fin k => fibType σ = m).card • w m
      ≤ ((univ : Finset (Fin N → Fin k)).image fibType).card • (fibTypeCount N k n * w n) :=
        Finset.sum_le_card_nsmul _ _ _ fun m hm => hbound m hm
    _ ≤ (N + 1) ^ k * (fibTypeCount N k n * w n) := by
        rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ himage

end TypeEvent

/-! #### The type event -/

section TypeEventMeasure

variable {N k : ℕ}

lemma prod_comp_eq_prod_pow_fibType {M : Type*} [CommMonoid M] (f : Fin k → M)
    (σ : Fin N → Fin k) : ∏ i, f (σ i) = ∏ j, f j ^ fibType σ j := by
  rw [← Finset.prod_fiberwise univ σ (fun i => f (σ i))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
  rfl

/-- The box of an assignment `σ`: coordinate `i` lies in `I (σ i)`. -/
def fibTypeBox (I : Fin k → Set ℝ) (σ : Fin N → Fin k) : Set (Fin N → ℝ) :=
  Set.univ.pi fun i => I (σ i)

lemma fibTypeBox_sub_event (I : Fin k → Set ℝ) [∀ j, DecidablePred (· ∈ I j)]
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ} {σ : Fin N → Fin k} (hσ : fibType σ = n) :
    fibTypeBox I σ ⊆ {v | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} := by
  intro v hv j
  have hv' : ∀ i, v i ∈ I (σ i) := fun i => hv i (Set.mem_univ i)
  show (univ.filter fun i => v i ∈ I j).card = n j
  rw [← hσ]
  unfold fibType
  congr 1
  refine Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => h ▸ hv' i⟩
  by_contra hne
  exact Set.disjoint_left.1 (hdisj hne) (hv' i) h

lemma fibTypeBox_disjoint {I : Fin k → Set ℝ} (hdisj : Pairwise fun j j' => Disjoint (I j) (I j'))
    {σ σ' : Fin N → Fin k} (h : σ ≠ σ') : Disjoint (fibTypeBox I σ) (fibTypeBox I σ') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  rw [Set.disjoint_left]
  intro v hv hv'
  exact Set.disjoint_left.1 (hdisj hi) (hv i (Set.mem_univ i)) (hv' i (Set.mem_univ i))

lemma volume_fibTypeBoxes (I : Fin k → Set ℝ) (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) (ℓ : Fin k → ℝ)
    (hℓ : ∀ j, volume (I j) = ENNReal.ofReal (ℓ j)) (hℓ0 : ∀ j, 0 ≤ ℓ j) (n : Fin k → ℕ) :
    volume (⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), fibTypeBox I σ) =
      ENNReal.ofReal (fibTypeCount N k n * ∏ j, ℓ j ^ n j) := by
  rw [measure_biUnion_finset (fun σ _ σ' _ h => fibTypeBox_disjoint hdisj h)
    (fun σ _ => MeasurableSet.univ_pi fun i => hI (σ i))]
  have hbox : ∀ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n),
      volume (fibTypeBox I σ) = ENNReal.ofReal (∏ j, ℓ j ^ n j) := by
    intro σ hσ
    rw [fibTypeBox, volume_pi_pi, Finset.prod_congr rfl fun i _ => hℓ (σ i),
      ← ENNReal.ofReal_prod_of_nonneg fun i _ => hℓ0 _, prod_comp_eq_prod_pow_fibType,
      (Finset.mem_filter.1 hσ).2]
  rw [Finset.sum_congr rfl hbox, Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rfl

/-- `exp (-N Σ α_j log (α_j/ℓ_j)) = N^N ∏ ℓ_j^{n_j} / ∏ n_j^{n_j}`, `α_j = n_j / N`. -/
lemma exp_type_rate (ℓ : Fin k → ℝ) (hℓpos : ∀ j, 0 < ℓ j) (n : Fin k → ℕ)
    (hn : ∑ j, n j = N) :
    Real.exp (-(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j))) =
      (N : ℝ) ^ N * (∏ j, ℓ j ^ n j) / ∏ j, (n j : ℝ) ^ n j := by
  have hnN : ∀ j, (N : ℝ) * ((n j : ℝ) / N) = n j := by
    intro j
    rcases Nat.eq_zero_or_pos N with h | h
    · have : n j = 0 := by
        have := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (mem_univ j)
        omega
      simp [this, h]
    · have : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      field_simp
  have e1 : -(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j)) =
      ∑ j, -((n j : ℝ) * Real.log (((n j : ℝ) / N) / ℓ j)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hnN]
  have e2 : ∀ j, Real.exp (-((n j : ℝ) * Real.log (((n j : ℝ) / N) / ℓ j))) =
      (N : ℝ) ^ n j * ℓ j ^ n j / (n j : ℝ) ^ n j := by
    intro j
    rcases Nat.eq_zero_or_pos (n j) with h | h
    · simp [h]
    · have hN : (0 : ℝ) < N := by
        have := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (mem_univ j)
        exact_mod_cast (show 0 < N by omega)
      have hz : 0 < ((n j : ℝ) / N) / ℓ j := by
        have : (0 : ℝ) < n j := by exact_mod_cast h
        exact div_pos (div_pos this hN) (hℓpos j)
      rw [← neg_mul, exp_neg_nat_mul_log hz, inv_div, div_div_eq_mul_div, div_pow, mul_pow]
      ring
  rw [e1, Real.exp_sum, Finset.prod_congr rfl fun j _ => e2 j, Finset.prod_div_distrib,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hn]

/-- The numerical part of the type bound: `exp (-N Σ α log (α/ℓ)) / (N+1)^k ≤ #T(n) ∏ ℓ^n`. -/
lemma type_exp_le (ℓ : Fin k → ℝ) (hℓpos : ∀ j, 0 < ℓ j) (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    Real.exp (-(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j))) /
        ((N : ℝ) + 1) ^ k ≤ fibTypeCount N k n * ∏ j, ℓ j ^ n j := by
  have hC := pow_le_fibTypeCount n hn
  have hC' : (N : ℝ) ^ N ≤ ((N : ℝ) + 1) ^ k * (fibTypeCount N k n * ∏ j, (n j : ℝ) ^ n j) := by
    exact_mod_cast hC
  have hnn : 0 < ∏ j, (n j : ℝ) ^ n j := Finset.prod_pos fun j _ => by
    rcases Nat.eq_zero_or_pos (n j) with h | h
    · simp [h]
    · have : (0 : ℝ) < n j := by exact_mod_cast h
      positivity
  have hℓ : 0 ≤ ∏ j, ℓ j ^ n j := Finset.prod_nonneg fun j _ => pow_nonneg (hℓpos j).le _
  rw [exp_type_rate ℓ hℓpos n hn, div_div, div_le_iff₀ (by positivity)]
  calc (N : ℝ) ^ N * ∏ j, ℓ j ^ n j
      ≤ ((N : ℝ) + 1) ^ k * (fibTypeCount N k n * ∏ j, (n j : ℝ) ^ n j) * ∏ j, ℓ j ^ n j :=
        mul_le_mul_of_nonneg_right hC' hℓ
    _ = _ := by ring

/-- **Type event lower bound** (blueprint A4, `type_event_ge`). For pairwise disjoint measurable
sets `I j` of volume `ℓ j > 0` (e.g. rational intervals) and counts `n j` summing to `N`,
with `α j = n j / N`:
`volume {v | ∀ j, #{i | v i ∈ I j} = n j} ≥ exp (-N Σ_j α_j log (α_j/ℓ_j)) / (N+1)^k`. -/
theorem type_event_ge (I : Fin k → Set ℝ) [∀ j, DecidablePred (· ∈ I j)]
    (hI : ∀ j, MeasurableSet (I j)) (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) (ℓ : Fin k → ℝ)
    (hℓ : ∀ j, volume (I j) = ENNReal.ofReal (ℓ j)) (hℓpos : ∀ j, 0 < ℓ j)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    ENNReal.ofReal (Real.exp (-(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j))) /
        ((N : ℝ) + 1) ^ k) ≤
      volume {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} :=
  calc _ ≤ ENNReal.ofReal (fibTypeCount N k n * ∏ j, ℓ j ^ n j) :=
        ENNReal.ofReal_le_ofReal (type_exp_le ℓ hℓpos n hn)
    _ = volume (⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), fibTypeBox I σ) :=
        (volume_fibTypeBoxes I hI hdisj ℓ hℓ (fun j => (hℓpos j).le) n).symm
    _ ≤ _ := measure_mono (Set.iUnion₂_subset fun _ hσ =>
        fibTypeBox_sub_event I hdisj (Finset.mem_filter.1 hσ).2)

/-- **Type event lower bound for a uniform row** (sets inside `[0,1]`). -/
theorem type_event_ge_rowM (I : Fin k → Set ℝ) [∀ j, DecidablePred (· ∈ I j)]
    (hI : ∀ j, MeasurableSet (I j)) (hdisj : Pairwise fun j j' => Disjoint (I j) (I j'))
    (hsub : ∀ j, I j ⊆ Set.Icc 0 1) (ℓ : Fin k → ℝ)
    (hℓ : ∀ j, volume (I j) = ENNReal.ofReal (ℓ j)) (hℓpos : ∀ j, 0 < ℓ j)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    ENNReal.ofReal (Real.exp (-(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j))) /
        ((N : ℝ) + 1) ^ k) ≤
      rowM N {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} := by
  rw [← restrict_row, Measure.restrict_apply' measurableSet_cubeRow]
  calc _ ≤ ENNReal.ofReal (fibTypeCount N k n * ∏ j, ℓ j ^ n j) :=
        ENNReal.ofReal_le_ofReal (type_exp_le ℓ hℓpos n hn)
    _ = volume (⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), fibTypeBox I σ) :=
        (volume_fibTypeBoxes I hI hdisj ℓ hℓ (fun j => (hℓpos j).le) n).symm
    _ ≤ _ := measure_mono (Set.iUnion₂_subset fun σ hσ => Set.subset_inter
        (fibTypeBox_sub_event I hdisj (Finset.mem_filter.1 hσ).2)
        (show fibTypeBox I σ ⊆ cubeRow N from fun v hv i _ => hsub (σ i) (hv i (Set.mem_univ i))))

/-- Sorted half-open intervals are pairwise disjoint. -/
lemma pairwise_disjoint_Ico {a b : Fin k → ℝ} (hsort : ∀ j j', j < j' → b j ≤ a j') :
    Pairwise fun j j' => Disjoint (Set.Ico (a j) (b j)) (Set.Ico (a j') (b j')) := by
  intro j j' hjj'
  rcases lt_or_gt_of_ne hjj' with h | h
  · exact Set.Ico_disjoint_Ico.2 ((min_le_left _ _).trans ((hsort j j' h).trans (le_max_right _ _)))
  · exact Set.Ico_disjoint_Ico.2 ((min_le_right _ _).trans ((hsort j' j h).trans (le_max_left _ _)))

/-- **Type event with sorted intervals `[a j, b j)` inside `[0,1]`** (the grid form used by the
certificate C1), under the row law. -/
theorem type_event_ge_Ico (a b : Fin k → ℝ) (hab : ∀ j, a j < b j)
    (hsort : ∀ j j', j < j' → b j ≤ a j') (ha0 : ∀ j, 0 ≤ a j) (hb1 : ∀ j, b j ≤ 1)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    ENNReal.ofReal (Real.exp (-(N * ∑ j, ((n j : ℝ) / N) *
        Real.log (((n j : ℝ) / N) / (b j - a j)))) / ((N : ℝ) + 1) ^ k) ≤
      rowM N {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ Set.Ico (a j) (b j)).card = n j} :=
  type_event_ge_rowM (fun j => Set.Ico (a j) (b j)) (fun _ => measurableSet_Ico)
    (pairwise_disjoint_Ico hsort) (fun j => Set.Ico_subset_Icc_self.trans
      (Set.Icc_subset_Icc (ha0 j) (hb1 j))) (fun j => b j - a j) (fun _ => Real.volume_Ico)
    (fun j => sub_pos.2 (hab j)) n hn

/-- Events of two distinct rows are independent under `cubeM N`. -/
lemma cubeM_two_rows {r1 r2 : State N} (h : r1 ≠ r2) {A B : Set (Fin N → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cubeM N {w | w r1 ∈ A ∧ w r2 ∈ B} = rowM N A * rowM N B := by
  have hind : IndepFun (fun w : Param N => w r1) (fun w => w r2) (cubeM N) :=
    (iIndepFun_rows (fun _ v => v) fun _ => measurable_id).indepFun h
  have := hind.measure_inter_preimage_eq_mul A B hA hB
  have hmp : ∀ r, MeasurePreserving (fun w : Param N => w r) (cubeM N) (rowM N) := fun r =>
    measurePreserving_eval (fun _ : State N => rowM N) r
  rw [(hmp r1).measure_preimage hA.nullMeasurableSet,
    (hmp r2).measure_preimage hB.nullMeasurableSet] at this
  exact this

end TypeEventMeasure

/-! ### Rational bounds on `exp` and `log` -/

section RatBounds

/-- The Taylor polynomial `∑_{m < n} q^m / m!` of `exp` at a rational point. -/
def expTay (q : ℚ) (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, q ^ m / m.factorial

/-- The remainder bound `|q|^n (n+1)/(n! n)` of `Real.exp_bound`. -/
def expErr (q : ℚ) (n : ℕ) : ℚ := |q| ^ n * (((n : ℚ) + 1) / (n.factorial * n))

lemma expTay_cast (q : ℚ) (n : ℕ) :
    ((expTay q n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (q : ℝ) ^ m / m.factorial := by
  simp [expTay]

lemma expErr_cast (q : ℚ) (n : ℕ) :
    ((expErr q n : ℚ) : ℝ) = |(q : ℝ)| ^ n * (n.succ / (n.factorial * n)) := by
  simp [expErr]

/-- `Real.exp_bound` at a rational point. -/
lemma abs_exp_sub_expTay {q : ℚ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.exp q - expTay q n| ≤ expErr q n := by
  have := Real.exp_bound (x := (q : ℝ)) (by exact_mod_cast hq) hn
  rwa [expTay_cast, expErr_cast]

lemma exp_rat_pow (q : ℚ) {m : ℕ} (hm : 0 < m) :
    Real.exp q = Real.exp ((q / m : ℚ) : ℝ) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma abs_div_nat_le_one {q : ℚ} {m : ℕ} (hm : 0 < m) (hq : |q| ≤ m) : |q / m| ≤ 1 := by
  rw [abs_div, Nat.abs_cast, div_le_one (by exact_mod_cast hm)]
  exact hq

/-- **Upper bound on `exp`** at a rational point, by the Taylor bound at `q/m` and `m`-th power
(`|q| ≤ m`). The hypothesis `h` is a decidable rational inequality. -/
theorem exp_le_rat {q r : ℚ} (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hq : |q| ≤ m)
    (h : (expTay (q / m) n + expErr (q / m) n) ^ m ≤ r) : Real.exp q ≤ r := by
  have h1 := abs_exp_sub_expTay (abs_div_nat_le_one hm hq) hn
  have h2 : Real.exp ((q / m : ℚ) : ℝ) ≤ ((expTay (q / m) n + expErr (q / m) n : ℚ) : ℝ) := by
    push_cast at h1 ⊢; linarith [(abs_le.1 h1).2]
  rw [exp_rat_pow q hm]
  calc Real.exp ((q / m : ℚ) : ℝ) ^ m ≤ ((expTay (q / m) n + expErr (q / m) n : ℚ) : ℝ) ^ m :=
        pow_le_pow_left₀ (Real.exp_pos _).le h2 m
    _ ≤ r := by exact_mod_cast h

/-- **Lower bound on `exp`** at a rational point (`|q| ≤ m`). -/
theorem rat_le_exp {q r : ℚ} (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hq : |q| ≤ m)
    (h0 : 0 ≤ expTay (q / m) n - expErr (q / m) n)
    (h : r ≤ (expTay (q / m) n - expErr (q / m) n) ^ m) : (r : ℝ) ≤ Real.exp q := by
  have h1 := abs_exp_sub_expTay (abs_div_nat_le_one hm hq) hn
  have h2 : ((expTay (q / m) n - expErr (q / m) n : ℚ) : ℝ) ≤ Real.exp ((q / m : ℚ) : ℝ) := by
    push_cast at h1 ⊢; linarith [(abs_le.1 h1).1]
  rw [exp_rat_pow q hm]
  calc (r : ℝ) ≤ ((expTay (q / m) n - expErr (q / m) n : ℚ) : ℝ) ^ m := by exact_mod_cast h
    _ ≤ _ := pow_le_pow_left₀ (by exact_mod_cast h0) h2 m

/-- **Upper bound on `log`** at a positive rational point: `log x ≤ r` as soon as `x` is below
the rational lower bound of `exp r`. -/
theorem log_le_rat {x r : ℚ} (hx : 0 < x) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hr : |r| ≤ m)
    (h0 : 0 ≤ expTay (r / m) n - expErr (r / m) n)
    (h : x ≤ (expTay (r / m) n - expErr (r / m) n) ^ m) : Real.log x ≤ r := by
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hx)]
  exact rat_le_exp n m hn hm hr h0 h

/-- **Lower bound on `log`** at a positive rational point: `r ≤ log x` as soon as the rational
upper bound of `exp r` is below `x`. -/
theorem log_ge_rat {x r : ℚ} (hx : 0 < x) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hr : |r| ≤ m)
    (h : (expTay (r / m) n + expErr (r / m) n) ^ m ≤ x) : (r : ℝ) ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by exact_mod_cast hx)]
  exact exp_le_rat n m hn hm hr h

/-- Sanity check of the rational bounds: `0.4054 < log (3/2) < 0.4055` (so `x0 ∈ (0.2027, 0.20275)`). -/
lemma log_three_halves_bounds :
    ((2027 / 5000 : ℚ) : ℝ) ≤ Real.log ((3 / 2 : ℚ) : ℝ) ∧
      Real.log ((3 / 2 : ℚ) : ℝ) ≤ ((811 / 2000 : ℚ) : ℝ) :=
  ⟨log_ge_rat (by norm_num) 8 1 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
    log_le_rat (by norm_num) 8 1 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)⟩

end RatBounds

/-! ### From the template to rates; Riemann cells; many light rows -/

section Rates

variable {N : ℕ}

/-- **Template in real numbers**: if the two per-column integrals of `joint_template` are at most
`J` and `Ex`, the probability is at most `e^{t B} (J Ex)^N`. -/
theorem joint_template_real (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (ell ellU : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (hell : Measurable ell) (hellU : Measurable ellU)
    (hg : Measurable fun p : ℝ × ℝ => g p.1 p.2) (W : Set ℝ) (hW : MeasurableSet W)
    (B t lamU lam : ℝ) (ht : 0 ≤ t) (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) {J Ex : ℝ}
    (hJ0 : 0 ≤ J) (hE0 : 0 ≤ Ex)
    (hJ : ∫⁻ y in W, ENNReal.ofReal (Real.exp ((lamU - t) * ell y)) *
      ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g y u)) ∂unif ∂unif ≤ ENNReal.ofReal J)
    (hE : ∫⁻ x, ENNReal.ofReal (Real.exp (-lamU * ellU x)) ∂unif ≤ ENNReal.ofReal Ex) :
    cubeM N {w | (∀ i, w (ra i) i ∈ W) ∧ ∑ i, ell (w (ra i) i) ≤ B ∧
        ∑ i, ellU (w (rc i) i) ≤ ∑ i, ell (w (ra i) i) ∧ ∑ i, g (w (ra i) i) (w (rb i) i) ≤ 0} ≤
      ENNReal.ofReal (Real.exp (t * B) * (J * Ex) ^ N) := by
  refine (joint_template ra rb rc hab hac hbc ell ellU g hell hellU hg W hW B t lamU lam ht hlamU
    hlam).trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (mul_nonneg hJ0 hE0),
    ENNReal.ofReal_mul hJ0]
  gcongr

/-- **Per-coordinate rate to an exponential bound**: if
`log 2 + log J + log Ex + t x0 ≤ -R` (the form of the certificate soundness lemma), then
`2^N e^{t x0 N} (J Ex)^N ≤ e^{-R N}` (the `2^N` pays for the union over the heavy row). -/
theorem rate_of_log_le {J Ex t x0 R : ℝ} (hJ : 0 < J) (hE : 0 < Ex)
    (hlog : Real.log 2 + Real.log J + Real.log Ex + t * x0 ≤ -R) (N : ℕ) :
    (2 : ℝ) ^ N * (Real.exp (t * (x0 * N)) * (J * Ex) ^ N) ≤ Real.exp (-(R * N)) := by
  have h1 : 2 * (Real.exp (t * x0) * (J * Ex)) ≤ Real.exp (-R) := by
    calc 2 * (Real.exp (t * x0) * (J * Ex))
        = Real.exp (Real.log 2 + Real.log J + Real.log Ex + t * x0) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
            Real.exp_log hJ, Real.exp_log hE]
          ring
      _ ≤ Real.exp (-R) := Real.exp_le_exp.2 hlog
  have h2 := pow_le_pow_left₀ (by positivity) h1 N
  calc (2 : ℝ) ^ N * (Real.exp (t * (x0 * N)) * (J * Ex) ^ N)
      = (2 * (Real.exp (t * x0) * (J * Ex))) ^ N := by
        have : Real.exp (t * (x0 * N)) = Real.exp (t * x0) ^ N := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [this]; ring
    _ ≤ Real.exp (-R) ^ N := h2
    _ = Real.exp (-(R * N)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- `unif` integrals over a set are at most Lebesgue integrals. -/
lemma setLIntegral_unif_le (s : Set ℝ) (f : ℝ → ENNReal) :
    ∫⁻ y in s, f y ∂unif ≤ ∫⁻ y in s, f y :=
  lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl

/-- **Riemann cells**: a set integral over `(c 0, c M]` is at most `∑ B_m (c (m+1) - c m)` when
`f ≤ B_m` on the cell `(c m, c (m+1)]` (monotone grid `c`). -/
theorem setLIntegral_Ioc_le_cells (c : ℕ → ℝ) (hc : Monotone c) (f : ℝ → ENNReal) (B : ℕ → ℝ) :
    ∀ M : ℕ, (∀ m < M, ∀ y ∈ Set.Ioc (c m) (c (m + 1)), f y ≤ ENNReal.ofReal (B m)) →
      ∫⁻ y in Set.Ioc (c 0) (c M), f y ≤
        ∑ m ∈ Finset.range M, ENNReal.ofReal (B m) * ENNReal.ofReal (c (m + 1) - c m)
  | 0, _ => by simp
  | M + 1, hB => by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (hc (Nat.zero_le M)) (hc (Nat.le_succ M)),
      lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc.2 (by simp)),
      Finset.sum_range_succ]
    gcongr
    · exact setLIntegral_Ioc_le_cells c hc f B M fun m hm => hB m (Nat.lt_succ_of_lt hm)
    · calc ∫⁻ y in Set.Ioc (c M) (c (M + 1)), f y
          ≤ ∫⁻ _y in Set.Ioc (c M) (c (M + 1)), ENNReal.ofReal (B M) :=
            setLIntegral_mono measurable_const fun y hy => hB M (Nat.lt_succ_self M) y hy
        _ = _ := by rw [setLIntegral_const, Real.volume_Ioc]

/-- **At least `K` rows in an event** (`K`-fold union over the row sets of size `K`, rows are
independent): `P(#{r | w r ∈ E} ≥ K) ≤ C(2^N, K) p^K` when each row is in `E` with probability
at most `p`. -/
theorem cubeM_card_rows_ge {E : Set (Fin N → ℝ)} [DecidablePred (· ∈ E)] (hE : MeasurableSet E)
    (K : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : rowM N E ≤ ENNReal.ofReal p) :
    cubeM N {w | K ≤ (univ.filter fun r : State N => w r ∈ E).card} ≤
      ENNReal.ofReal ((2 ^ N).choose K * p ^ K) := by
  have hsub : {w : Param N | K ≤ (univ.filter fun r : State N => w r ∈ E).card} ⊆
      ⋃ S ∈ Finset.powersetCard K (univ : Finset (State N)),
        ⋂ r ∈ S, (fun w : Param N => w r) ⁻¹' E := by
    intro w hw
    obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (show K ≤ _ from hw)
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, exists_prop]
    exact ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hSc⟩,
      fun r hr => (Finset.mem_filter.1 (hS hr)).2⟩
  have hind := iIndepFun_rows (N := N) (fun _ v => v) fun _ => measurable_id
  have hmp : ∀ r, MeasurePreserving (fun w : Param N => w r) (cubeM N) (rowM N) := fun r =>
    measurePreserving_eval (fun _ : State N => rowM N) r
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ S ∈ Finset.powersetCard K (univ : Finset (State N)),
        cubeM N (⋂ r ∈ S, (fun w : Param N => w r) ⁻¹' E)
      ≤ ∑ _S ∈ Finset.powersetCard K (univ : Finset (State N)), ENNReal.ofReal (p ^ K) := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [hind.measure_inter_preimage_eq_mul S (sets := fun _ => E) fun _ _ => hE]
        calc ∏ r ∈ S, cubeM N ((fun w : Param N => w r) ⁻¹' E)
            = ∏ _r ∈ S, rowM N E :=
              Finset.prod_congr rfl fun r _ => (hmp r).measure_preimage hE.nullMeasurableSet
          _ ≤ ∏ _r ∈ S, ENNReal.ofReal p := Finset.prod_le_prod' fun _ _ => hp
          _ = ENNReal.ofReal (p ^ K) := by
              rw [Finset.prod_const, (Finset.mem_powersetCard.1 hS).2, ENNReal.ofReal_pow hp0]
    _ = ENNReal.ofReal ((2 ^ N).choose K * p ^ K) := by
        rw [Finset.sum_const, Finset.card_powersetCard, card_state, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact le_rfl

/-- **Many light rows** (blueprint G6(d), C11): at least `K` rows with `∑_i -log ≤ x` has
probability at most `(2^N e^{-N (x/N - 1 - log (x/N))})^K`, for `0 < x ≤ N`. -/
theorem cubeM_many_light_rows (K : ℕ) {x : ℝ} (hx : 0 < x) (hxN : x ≤ N) :
    cubeM N {w | K ≤ (univ.filter fun r : State N =>
        ∑ i, -Real.log (clamp01 (w r i)) ≤ x).card} ≤
      ENNReal.ofReal ((2 ^ N * Real.exp (-(N * (x / N - 1 - Real.log (x / N))))) ^ K) := by
  set p := Real.exp (-(N * (x / N - 1 - Real.log (x / N))))
  have hE : MeasurableSet {v : Fin N → ℝ | ∑ i, -Real.log (clamp01 (v i)) ≤ x} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ =>
      measurable_negLogClamp.comp (measurable_pi_apply i)) measurable_const
  have hp : rowM N {v : Fin N → ℝ | ∑ i, -Real.log (clamp01 (v i)) ≤ x} ≤ ENNReal.ofReal p := by
    have := rowM_negLog_sum_le (N := N) univ hx (by simpa using hxN)
    simpa using this
  refine (measure_mono ?_).trans ((cubeM_card_rows_ge hE K (Real.exp_pos _).le hp).trans
    (ENNReal.ofReal_le_ofReal ?_))
  · intro w hw
    have heq : (univ.filter fun r : State N =>
        w r ∈ {v : Fin N → ℝ | ∑ i, -Real.log (clamp01 (v i)) ≤ x}) =
        univ.filter fun r : State N => ∑ i, -Real.log (clamp01 (w r i)) ≤ x :=
      Finset.filter_congr fun r _ => Iff.rfl
    show K ≤ (univ.filter fun r : State N =>
      w r ∈ {v : Fin N → ℝ | ∑ i, -Real.log (clamp01 (v i)) ≤ x}).card
    rw [heq]; exact hw
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Real.exp_pos _).le _)
  exact_mod_cast Nat.choose_le_pow _ _

end Rates

end

end Census
end IIT
