/-
Census, B1, W14 work package WP4 (fresh K-free events), part A: generic tools and FE0.

* `lowerTail_nonneg` (one-sided lower tail for `[0,1]`-valued independent summands, from `chernoff_indep`
  and `e^{-y} ≤ 1 - y + y²/2`), and its form with a variance bound `lowerTail_nonneg_V`;
* `multChernoff_lower` (`P(Σ Y ≤ m0/2) ≤ e^{-m0/8}` for `[0,1]`-valued independent summands of mean
  `≥ m0`, from the convexity bound `e^{-y ln 2} ≤ 1 - y/2`);
* `iIndepFun_pi_blocks`: functions of pairwise disjoint coordinate blocks of a finite product measure are
  independent (from `B1Prod.pi_iInter_eq_prod_of_detOn`);
* `frA_cheb_rows`: Chebyshev under `cubeM` for a sum of (row-dependent) functions of the rows;
* the transfer of fresh events to `cubeM` (`frA_transfer`), and real-analysis absorbers
  (`frA_ev_logsq`, `(N+1)^k ≤ e^{k(ln N + 1)}`, `Nat.log 2 N ≤ 2 ln N`);
* **`freshFE0`**.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §9.  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped Classical

/-! ### 1. Generic tails -/

section Generic

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma frA_integrable_Icc {X : Ω → ℝ} (hm : Measurable X) (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable X μ :=
  Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hX ω).1]; exact (hX ω).2)

lemma frA_integrable_sq_Icc {X : Ω → ℝ} (hm : Measurable X) (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => X ω ^ 2) μ :=
  Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
    have h0 := (hX ω).1
    have h1 := (hX ω).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith)

/-- One factor of the lower-tail Chernoff bound. -/
lemma frA_lt_factor {X : Ω → ℝ} (hm : Measurable X) (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * X ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (-t * (∫ ω, X ω ∂μ) + t ^ 2 / 2 * ∫ ω, X ω ^ 2 ∂μ)) := by
  have h1 : Integrable X μ := frA_integrable_Icc hm hX
  have h2 : Integrable (fun ω => X ω ^ 2) μ := frA_integrable_sq_Icc hm hX
  have hq : Integrable (fun ω => 1 + (-t) * X ω + t ^ 2 / 2 * X ω ^ 2) μ :=
    ((integrable_const 1).add (h1.const_mul (-t))).add (h2.const_mul (t ^ 2 / 2))
  have hq0 : ∀ ω, 0 ≤ 1 + (-t) * X ω + t ^ 2 / 2 * X ω ^ 2 := fun ω => by
    nlinarith [sq_nonneg (t * X ω - 1)]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * X ω)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (1 + (-t) * X ω + t ^ 2 / 2 * X ω ^ 2) ∂μ := by
        refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
        have := fa_exp_neg_le (t * X ω) (mul_nonneg ht (hX ω).1)
        have e : -t * X ω = -(t * X ω) := by ring
        rw [e]
        nlinarith
    _ = ENNReal.ofReal (∫ ω, (1 + (-t) * X ω + t ^ 2 / 2 * X ω ^ 2) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hq (ae_of_all _ hq0)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hA : Integrable (fun ω => 1 + -t * X ω) μ := (integrable_const 1).add (h1.const_mul (-t))
        have hB : Integrable (fun ω => t ^ 2 / 2 * X ω ^ 2) μ := h2.const_mul _
        have hC : Integrable (fun ω => -t * X ω) μ := h1.const_mul (-t)
        rw [integral_add hA hB, integral_add (integrable_const 1) hC, integral_const, integral_const_mul,
          integral_const_mul]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        have := Real.add_one_le_exp (-t * (∫ ω, X ω ∂μ) + t ^ 2 / 2 * ∫ ω, X ω ^ 2 ∂μ)
        linarith

/-- **Lower tail for `[0,1]`-valued independent summands**, with a variance bound `V`. -/
theorem lowerTail_nonneg_V {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {a V : ℝ} (ha : 0 ≤ a)
    (hV : 0 < V) (hVs : ∑ i ∈ s, ∫ ω', X i ω' ^ 2 ∂μ ≤ V) :
    μ {ω | ∑ i ∈ s, X i ω ≤ ∑ i ∈ s, ∫ ω', X i ω' ∂μ - a} ≤
      ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * V)))) := by
  set t := a / V with ht
  have ht0 : 0 ≤ t := div_nonneg ha hV.le
  refine (chernoff_indep s hind hmeas (a := ∑ i ∈ s, ∫ ω', X i ω' ∂μ - a) ht0).trans ?_
  have hprod : ∏ i ∈ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * X i ω)) ∂μ ≤
      ∏ i ∈ s, ENNReal.ofReal (Real.exp (-t * (∫ ω, X i ω ∂μ) + t ^ 2 / 2 * ∫ ω, X i ω ^ 2 ∂μ)) :=
    prod_le_prod' fun i _ => frA_lt_factor (hmeas i) (hX i) ht0
  refine (mul_le_mul' le_rfl hprod).trans ?_
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hV2 : t ^ 2 / 2 * ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ t ^ 2 / 2 * V :=
    mul_le_mul_of_nonneg_left hVs (by positivity)
  have e : t * (∑ i ∈ s, ∫ ω', X i ω' ∂μ - a) + (-t * ∑ i ∈ s, ∫ ω, X i ω ∂μ) = -(t * a) := by ring
  have e2 : -(t * a) + t ^ 2 / 2 * V = -(a ^ 2 / (2 * V)) := by
    rw [ht]; field_simp; ring
  linarith

/-- **`lowerTail_nonneg`** (blueprint form): `P(Σ X ≤ Σ EX - a) ≤ exp(-a²/(2 Σ EX²))`. -/
theorem lowerTail_nonneg {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : 0 ≤ a) :
    μ {ω | ∑ i ∈ s, X i ω ≤ ∑ i ∈ s, ∫ ω', X i ω' ∂μ - a} ≤
      ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * ∑ i ∈ s, ∫ ω', X i ω' ^ 2 ∂μ)))) := by
  have h0 : 0 ≤ ∑ i ∈ s, ∫ ω', X i ω' ^ 2 ∂μ :=
    sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
  rcases h0.lt_or_eq with hpos | hz
  · exact lowerTail_nonneg_V s hind hmeas hX ha hpos le_rfl
  · rw [← hz, mul_zero, div_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one

lemma frA_exp_neg_log2_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp (-Real.log 2 * y) ≤ 1 - y / 2 := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-Real.log 2)) (sub_nonneg.2 h1) h0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at h
  have e : -Real.log 2 * y = y * -Real.log 2 := by ring
  rw [e]
  linarith

/-- **Multiplicative Chernoff lower tail** `P(Σ Y ≤ m0/2) ≤ e^{-m0/8}` (`Y_i ∈ [0,1]`, `Σ EY ≥ m0`). -/
theorem multChernoff_lower {X : ι → Ω → ℝ} (s : Finset ι) (hind : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {m0 : ℝ}
    (hm0 : 0 ≤ m0) (hmean : m0 ≤ ∑ i ∈ s, ∫ ω, X i ω ∂μ) :
    μ {ω | ∑ i ∈ s, X i ω ≤ m0 / 2} ≤ ENNReal.ofReal (Real.exp (-(m0 / 8))) := by
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine (chernoff_indep s hind hmeas (a := m0 / 2) hl0).trans ?_
  have hfac : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (-Real.log 2 * X i ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (-(∫ ω, X i ω ∂μ) / 2)) := by
    intro i
    have h1 : Integrable (X i) μ := frA_integrable_Icc (hmeas i) (hX i)
    have hq : Integrable (fun ω => 1 - X i ω / 2) μ := (integrable_const 1).sub (h1.div_const 2)
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-Real.log 2 * X i ω)) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (1 - X i ω / 2) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
            (frA_exp_neg_log2_le (hX i ω).1 (hX i ω).2)
      _ = ENNReal.ofReal (∫ ω, (1 - X i ω / 2) ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hq (ae_of_all _ fun ω =>
            show (0 : ℝ) ≤ 1 - X i ω / 2 by linarith [(hX i ω).2])).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_sub (integrable_const 1) (h1.div_const 2), integral_const, integral_div]
          simp only [probReal_univ, smul_eq_mul, one_mul]
          have := Real.add_one_le_exp (-(∫ ω, X i ω ∂μ) / 2)
          linarith
  refine (mul_le_mul' le_rfl (prod_le_prod' fun i _ => hfac i)).trans ?_
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hs : ∑ i ∈ s, -(∫ ω, X i ω ∂μ) / 2 = -(∑ i ∈ s, ∫ ω, X i ω ∂μ) / 2 := by
    rw [← sum_div, sum_neg_distrib]
  rw [hs]
  have hl : Real.log 2 < 3 / 4 := by have := Real.log_two_lt_d9; linarith
  nlinarith

end Generic

/-! ### 2. Independence of disjoint coordinate blocks -/

/-- Functions of pairwise disjoint coordinate blocks of a finite product measure are independent. -/
theorem iIndepFun_pi_blocks {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (C : κ → Finset ι)
    (hC : ∀ j k, j ≠ k → Disjoint (C j) (C k)) {Y : κ → (ι → E) → ℝ} (hY : ∀ k, Measurable (Y k))
    (hdet : ∀ k (ω ω' : ι → E), (∀ i ∈ C k, ω i = ω' i) → Y k ω = Y k ω') :
    iIndepFun Y (Measure.pi ν) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  exact pi_iInter_eq_prod_of_detOn ν S C (fun j _ k _ hjk => hC j k hjk)
    (fun j hj => hY j (hsets j hj))
    (fun j _ ω ω' h => by simp only [Set.mem_preimage]; rw [hdet j ω ω' h])

/-! ### 3. Chebyshev for sums over the rows -/

variable {N : ℕ}

lemma frA_cheb_rows (G : State N → (Fin N → ℝ) → ℝ) (hG : ∀ r, Measurable (G r))
    (hb : ∀ r v, |G r v| ≤ 1) {c : ℝ} (hc : 0 < c) :
    cubeM N {w | c ≤ |∑ r, G r (w r) - ∑ r, ∫ v, G r v ∂rowM N|} ≤
      ENNReal.ofReal ((∑ r, ∫ v, G r v ^ 2 ∂rowM N) / c ^ 2) := by
  have hmem : MemLp (fun w : Param N => ∑ r, G r (w r)) 2 (cubeM N) :=
    memLp_finsetSum _ fun r _ => memLp_row (hG r) (hb r) r
  have h := meas_ge_le_variance_div_sq hmem hc
  have hE : (∫ w, (fun w : Param N => ∑ r, G r (w r)) w ∂cubeM N) = ∑ r, ∫ v, G r v ∂rowM N := by
    rw [integral_finsetSum _ fun r _ => (memLp_row (hG r) (hb r) r).integrable one_le_two]
    exact sum_congr rfl fun r _ => integral_row_eval (hG r).aestronglyMeasurable r
  rw [hE] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  have hind := iIndepFun_rows G hG
  have hsum : (fun w : Param N => ∑ r, G r (w r)) = ∑ r, fun w : Param N => G r (w r) := by
    funext w; simp [Finset.sum_apply]
  rw [hsum, IndepFun.variance_sum (fun r _ => memLp_row (hG r) (hb r) r)
    (fun r _ r' _ hrr => hind.indepFun hrr)]
  refine sum_le_sum fun r _ => ?_
  refine (variance_le_expectation_sq (memLp_row (hG r) (hb r) r).aestronglyMeasurable).trans_eq ?_
  exact integral_row_eval (g := fun v => G r v ^ 2) ((hG r).pow_const 2).aestronglyMeasurable r

/-! ### 4. Transfer of fresh events to `cubeM` -/

lemma frA_glue_fresh (F : Finset (State N)) (f : F → Fin N → ℝ) (w : Param N) {r : State N}
    (hr : r ∉ F) : glueRows F f (restrOut F w) r = w r := by
  rw [glueRows_of_not_mem F f _ hr]; rfl

lemma frA_transfer (F : Finset (State N)) (f : F → Fin N → ℝ) (P : Param N → Prop)
    {B : Set (Param N)} (h : ∀ w, ¬ P (glueRows F f (restrOut F w)) → w ∈ B) :
    rowsOutM F {g | ¬ P (glueRows F f g)} ≤ cubeM N B := by
  have e := rowsOutM_glue_eq_cubeM F f {w | ¬ P w}
  calc rowsOutM F {g | ¬ P (glueRows F f g)} = cubeM N {w | ¬ P (glueRows F f (restrOut F w))} := e
    _ ≤ cubeM N B := measure_mono fun w hw => h w hw

/-! ### 5. Real-analysis absorbers -/

lemma frA_log_le_sqrt_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have h1 : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx.le]; ring
  rw [h1]
  have hp : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)
  have := Real.log_le_sub_one_of_pos hp
  linarith

/-- `A + B (ln N + 1)² ≤ δ N` eventually. -/
lemma frA_ev_logsq (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, A + B * (Real.log N + 1) ^ 2 ≤ δ * N := by
  set q0 : ℝ := (|A| + 25 * |B|) / δ + 1 with hq0
  have hq01 : 1 ≤ q0 := by rw [hq0]; have : 0 ≤ (|A| + 25 * |B|) / δ := by positivity
                           linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, q0 ^ 4 ≤ M := exists_nat_ge _
  filter_upwards [eventually_ge_atTop (max M 1)] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hNM : q0 ^ 4 ≤ N := hM.trans (by exact_mod_cast (le_max_left _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by linarith
  set u := Real.sqrt (Real.sqrt (N : ℝ)) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu4 : u ^ 4 = N := by
    rw [hu, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hNpos.le]
  have hu1 : 1 ≤ u := by
    by_contra h; replace h := not_le.mp h
    have : u ^ 4 < 1 := by
      calc u ^ 4 < 1 ^ 4 := pow_lt_pow_left₀ h hu0 (by norm_num)
        _ = 1 := one_pow _
    linarith
  have huq : q0 ≤ u ^ 2 := by
    by_contra h; replace h := not_le.mp h
    have h2 : u ^ 4 < q0 ^ 4 := by
      calc u ^ 4 = (u ^ 2) ^ 2 := by ring
        _ < q0 ^ 2 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
        _ ≤ q0 ^ 4 := pow_le_pow_right₀ hq01 (by norm_num)
    linarith
  have hlog : Real.log N + 1 ≤ 5 * u := by
    have := frA_log_le_sqrt_sqrt hNpos; linarith
  have hlog0 : 0 ≤ Real.log N + 1 := by have := Real.log_nonneg hN1; linarith
  have hsq : (Real.log N + 1) ^ 2 ≤ 25 * u ^ 2 := by nlinarith
  have hB : B * (Real.log N + 1) ^ 2 ≤ |B| * (25 * u ^ 2) :=
    calc B * (Real.log N + 1) ^ 2 ≤ |B| * (Real.log N + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg _)
      _ ≤ |B| * (25 * u ^ 2) := mul_le_mul_of_nonneg_left hsq (abs_nonneg B)
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have key : (|A| + 25 * |B|) * u ^ 2 ≤ δ * u ^ 4 := by
    have : (|A| + 25 * |B|) ≤ δ * u ^ 2 := by
      have h3 : (|A| + 25 * |B|) / δ ≤ u ^ 2 := by linarith
      rw [div_le_iff₀ hδ] at h3; linarith
    calc (|A| + 25 * |B|) * u ^ 2 ≤ δ * u ^ 2 * u ^ 2 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = δ * u ^ 4 := by ring
  have hA : A ≤ |A| * u ^ 2 := (le_abs_self A).trans (le_mul_of_one_le_right (abs_nonneg A) hu2)
  calc A + B * (Real.log N + 1) ^ 2 ≤ |A| * u ^ 2 + |B| * (25 * u ^ 2) := add_le_add hA hB
    _ ≤ δ * u ^ 4 := by linarith
    _ = δ * N := by rw [hu4]

lemma frA_log_succ_le {N : ℕ} (hN : 1 ≤ N) : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  have h : Real.log (((N : ℝ) + 1) / N) ≤ ((N : ℝ) + 1) / N - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) hpos.ne'] at h
  have : ((N : ℝ) + 1) / N - 1 ≤ 1 := by
    rw [div_sub_one hpos.ne', div_le_one hpos]; linarith
  linarith

lemma frA_pow_le_exp {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ((N : ℝ) + 1) ^ k ≤ Real.exp (k * (Real.log N + 1)) := by
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [← Real.exp_log (pow_pos hpos k), Real.log_pow]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (frA_log_succ_le hN) (Nat.cast_nonneg k))

lemma frA_natLog_le {N : ℕ} (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
  have h2 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2r : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h2
  have hl : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2r
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hk : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  nlinarith

lemma frA_log_nonneg (N : ℕ) : 0 ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- `J = 6 log₂ N + 16 ≤ 16 (ln N + 1)`. -/
lemma frA_JC_le {N : ℕ} (hN : 1 ≤ N) : (JC N : ℝ) ≤ 16 * (Real.log N + 1) := by
  have := frA_natLog_le hN
  have h0 := frA_log_nonneg N
  unfold JC; push_cast; linarith

/-! ### 6. FE0 -/

/-- **FE0**: the fresh entries lie in `(0,1)` almost surely. -/
theorem freshFE0 : FreshFieldProb FE0X (1 / 180) := by
  refine Eventually.of_forall fun N s r0 f => ?_
  refine (frA_transfer (sensRows s r0) f (FE0X N s r0) (B := (openCube N)ᶜ) fun w hw => ?_).trans ?_
  · intro hmem
    apply hw
    intro r hr i
    rw [frA_glue_fresh _ f w hr]
    exact hmem r i
  · rw [cubeM_compl_openCube]; exact bot_le

end Census
end IIT

#print axioms IIT.Census.lowerTail_nonneg
#print axioms IIT.Census.multChernoff_lower
#print axioms IIT.Census.iIndepFun_pi_blocks
#print axioms IIT.Census.frA_cheb_rows
#print axioms IIT.Census.frA_ev_logsq
#print axioms IIT.Census.freshFE0
