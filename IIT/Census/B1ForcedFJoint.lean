/-
Census, B1 forced joint bounds by independence (agent "forcedF").

* `cubeM_inter_indep`: an event reading only rows outside `F` is independent of an event reading only rows in `F`.
* `plusMean_fail_le`: for a finite set `F'` of `2^k - 1` rows (`k ∈ {1,2,3}`),
  `P(Σ_i log max(2(1 + Σ_{r∈F'} y_{r,i})/2^k, 1) > 0.46 N) ≤ e^{-N/32}` (column Chernoff, multiplier 1;
  `max(a,1) ≤ a + e^{μ(1-a)}/(eμ)` and the column moments).
* `joint_nuTcF`: the joint bound `JointBound P0NuTc` (effect side; the `K'`-subcube rows around `r0` other than `r0`
  are not read by the effect regime event for far `r0`).
-/
import IIT.Census.B1ForcedF0
import IIT.Census.B1ForcedFSelf

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset ProbabilityTheory

variable {N : ℕ}

/-! ### Independence of events on disjoint row sets -/

theorem cubeM_inter_indep (F : Finset (State N)) (X Y : Set (Param N))
    (hX : ∀ w w' : Param N, (∀ q, q ∉ F → w q = w' q) → w ∈ X → w' ∈ X)
    (hY : ∀ w w' : Param N, (∀ q ∈ F, w q = w' q) → w ∈ Y → w' ∈ Y) :
    cubeM N (X ∩ Y) = cubeM N X * cubeM N Y := by
  classical
  set H := restrOut F '' X
  set G := restrIn F '' Y
  have hXH : X = {w | restrOut F w ∈ H} := by
    ext w
    refine ⟨fun hw => ⟨w, hw, rfl⟩, ?_⟩
    rintro ⟨w', hw', he⟩
    refine hX w' w (fun q hq => ?_) hw'
    exact congrFun he ⟨q, hq⟩
  have hYG : Y = {w | restrIn F w ∈ G} := by
    ext w
    refine ⟨fun hw => ⟨w, hw, rfl⟩, ?_⟩
    rintro ⟨w', hw', he⟩
    refine hY w' w (fun q hq => ?_) hw'
    exact congrFun he ⟨q, hq⟩
  have hsplit : X ∩ Y = splitRowsE F ⁻¹' (G ×ˢ H) := by
    conv_lhs => rw [hXH, hYG]
    ext w; simp [splitRowsE_apply, and_comm]
  rw [hsplit, (mp_splitRows F).measure_preimage_equiv, Measure.prod_prod,
    ← cubeM_restrIn_preimage, ← cubeM_restrOut_preimage, ← hYG, ← hXH, mul_comm]

/-! ### Column integrals -/

lemma lintegral_colLaw_eval (r : State N) {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ c, f (c r) ∂colLaw N = ∫⁻ u, f u ∂unif := by
  rw [← colLaw_map_eval r, lintegral_map hf (measurable_pi_apply r)]

lemma lintegral_colLaw_prod (F' : Finset (State N)) {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ c, ∏ r ∈ F', f (c r) ∂colLaw N = (∫⁻ u, f u ∂unif) ^ F'.card := by
  have hind : iIndepFun (fun (r : State N) (c : State N → ℝ) => f (c r)) (colLaw N) :=
    iIndepFun_colLaw.comp (fun _ => f) (fun _ => hf)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun F' _ hind fun r => hf.comp (measurable_pi_apply r)]
  rw [Finset.prod_congr rfl fun r _ => lintegral_colLaw_eval r hf, Finset.prod_const]

lemma colLaw_isProb : IsProbabilityMeasure (colLaw N) := by
  unfold colLaw
  have : IsProbabilityMeasure unif := ⟨by rw [unif_univ]⟩
  infer_instance

lemma unif_isProb : IsProbabilityMeasure unif := ⟨by rw [unif_univ]⟩

/-- `z⁺ ≤ e^{μ z}/(e μ)`. -/
lemma pos_le_exp_div {z μ : ℝ} (hμ : 0 < μ) : max z 0 ≤ Real.exp (μ * z) / (Real.exp 1 * μ) := by
  rw [le_div_iff₀ (by positivity)]
  rcases le_total z 0 with h | h
  · rw [max_eq_right h, zero_mul]; positivity
  · rw [max_eq_left h]
    have := Real.add_one_le_exp (μ * z - 1)
    have e : Real.exp (μ * z) = Real.exp (μ * z - 1) * Real.exp 1 := by rw [← Real.exp_add]; ring_nf
    rw [e]
    have he := Real.exp_pos 1
    nlinarith

/-- **The column bound** for the subcube "plus" mean. -/
lemma col_maxPlus_le (F' : Finset (State N)) (k : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ∫⁻ c, ENNReal.ofReal (max (2 * (1 + ∑ r ∈ F', clamp01 (c r)) / 2 ^ k) 1) ∂colLaw N ≤
      ENNReal.ofReal (2 * (1 + F'.card / 2) / 2 ^ k +
        Real.exp (μ - 2 * μ / 2 ^ k) * ((Real.exp (2 * μ / 2 ^ k) - 1) / (2 * μ / 2 ^ k) *
          Real.exp (-(2 * μ / 2 ^ k))) ^ F'.card / (Real.exp 1 * μ)) := by
  haveI := colLaw_isProb (N := N)
  set κ : ℝ := 2 * μ / 2 ^ k with hκ
  have hκ0 : 0 < κ := by positivity
  set A : (State N → ℝ) → ℝ := fun c => 2 * (1 + ∑ r ∈ F', clamp01 (c r)) / 2 ^ k with hA
  -- pointwise: max(a,1) ≤ a + e^{μ(1-a)}/(eμ)
  have hpt : ∀ c, ENNReal.ofReal (max (A c) 1) ≤
      ENNReal.ofReal (2 / 2 ^ k) + ∑ r ∈ F', ENNReal.ofReal (2 / 2 ^ k * clamp01 (c r)) +
        ENNReal.ofReal (Real.exp (μ - κ) / (Real.exp 1 * μ)) *
          ∏ r ∈ F', ENNReal.ofReal (Real.exp (-κ * clamp01 (c r))) := by
    intro c
    have h1 : max (A c) 1 ≤ A c + Real.exp (μ * (1 - A c)) / (Real.exp 1 * μ) := by
      have := pos_le_exp_div (z := 1 - A c) hμ
      rcases le_total (A c) 1 with h | h
      · rw [max_eq_right h]; rw [max_eq_left (by linarith)] at this; linarith
      · rw [max_eq_left h]; have : 0 ≤ Real.exp (μ * (1 - A c)) / (Real.exp 1 * μ) := by positivity
        linarith
    have h2 : Real.exp (μ * (1 - A c)) = Real.exp (μ - κ) * ∏ r ∈ F', Real.exp (-κ * clamp01 (c r)) := by
      rw [← Real.exp_sum, ← Real.exp_add]; congr 1
      simp only [hA, hκ]; rw [← Finset.mul_sum]
      field_simp; ring
    have h3 : A c = 2 / 2 ^ k + ∑ r ∈ F', 2 / 2 ^ k * clamp01 (c r) := by
      simp only [hA]; rw [← Finset.mul_sum]; ring
    have hcl : ∀ r ∈ F', 0 ≤ 2 / 2 ^ k * clamp01 (c r) := fun r _ => mul_nonneg (by positivity) (clamp01_nonneg _)
    calc ENNReal.ofReal (max (A c) 1)
        ≤ ENNReal.ofReal (A c + Real.exp (μ * (1 - A c)) / (Real.exp 1 * μ)) := ENNReal.ofReal_le_ofReal h1
      _ = _ := by
          rw [h2, h3, ENNReal.ofReal_add (add_nonneg (by positivity) (Finset.sum_nonneg hcl)) (by positivity),
            ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg hcl), ENNReal.ofReal_sum_of_nonneg hcl,
            show Real.exp (μ - κ) * (∏ r ∈ F', Real.exp (-κ * clamp01 (c r))) / (Real.exp 1 * μ) =
              Real.exp (μ - κ) / (Real.exp 1 * μ) * ∏ r ∈ F', Real.exp (-κ * clamp01 (c r)) by ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg (fun r _ => (Real.exp_pos _).le)]
  have hm1 : ∀ r, Measurable fun c : State N → ℝ => ENNReal.ofReal (2 / 2 ^ k * clamp01 (c r)) :=
    fun r => ENNReal.measurable_ofReal.comp (measurable_const.mul (clamp01_measurable.comp (measurable_pi_apply r)))
  have hfe : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-κ * clamp01 u)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (clamp01_measurable.const_mul _))
  have hm2 : Measurable fun c : State N → ℝ => ∏ r ∈ F', ENNReal.ofReal (Real.exp (-κ * clamp01 (c r))) :=
    Finset.measurable_prod _ fun r _ => hfe.comp (measurable_pi_apply r)
  have hlin : ∫⁻ u, ENNReal.ofReal (2 / 2 ^ k * clamp01 u) ∂unif = ENNReal.ofReal (2 / 2 ^ k * (1 / 2)) := by
    have := lintegral_unif_pow 1
    simp only [pow_one] at this
    rw [show (fun u : ℝ => ENNReal.ofReal (2 / 2 ^ k * clamp01 u)) =
        fun u => ENNReal.ofReal (2 / 2 ^ k) * ENNReal.ofReal (clamp01 u) from
      funext fun u => ENNReal.ofReal_mul (by positivity),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, this,
      ← ENNReal.ofReal_mul (by positivity)]
    norm_num
  have hexp : ∫⁻ u, ENNReal.ofReal (Real.exp (-κ * clamp01 u)) ∂unif =
      ENNReal.ofReal ((Real.exp κ - 1) / κ * Real.exp (-κ)) := by
    rw [lintegral_unif_exp (by linarith : -κ ≠ 0)]
    congr 1
    have hk1 : Real.exp (-κ) * Real.exp κ = 1 := by rw [← Real.exp_add]; simp
    field_simp
    nlinarith [hk1]
  calc ∫⁻ c, ENNReal.ofReal (max (A c) 1) ∂colLaw N
      ≤ ∫⁻ c, (ENNReal.ofReal (2 / 2 ^ k) + ∑ r ∈ F', ENNReal.ofReal (2 / 2 ^ k * clamp01 (c r)) +
          ENNReal.ofReal (Real.exp (μ - κ) / (Real.exp 1 * μ)) *
            ∏ r ∈ F', ENNReal.ofReal (Real.exp (-κ * clamp01 (c r)))) ∂colLaw N := lintegral_mono hpt
    _ = ENNReal.ofReal (2 / 2 ^ k) + ∑ r ∈ F', ENNReal.ofReal (2 / 2 ^ k * (1 / 2)) +
          ENNReal.ofReal (Real.exp (μ - κ) / (Real.exp 1 * μ)) *
            ENNReal.ofReal ((Real.exp κ - 1) / κ * Real.exp (-κ)) ^ F'.card := by
        rw [lintegral_add_right _ (hm2.const_mul _), lintegral_add_right _ (Finset.measurable_sum _ fun r _ => hm1 r),
          lintegral_const, measure_univ, mul_one, lintegral_finsetSum _ fun r _ => hm1 r,
          lintegral_const_mul _ hm2, lintegral_colLaw_prod F' hfe, hexp]
        congr 2
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [lintegral_colLaw_eval (f := fun u => ENNReal.ofReal (2 / 2 ^ k * clamp01 u)) r
          (ENNReal.measurable_ofReal.comp (measurable_const.mul clamp01_measurable)), hlin]
    _ = _ := by
        have hq : 0 ≤ (Real.exp κ - 1) / κ * Real.exp (-κ) := by
          have : 1 ≤ Real.exp κ := Real.one_le_exp hκ0.le
          exact mul_nonneg (div_nonneg (by linarith) hκ0.le) (Real.exp_pos _).le
        rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_pow hq, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-! ### The subcube "plus" mean: failure probability -/

/-- The failure event of the subcube "plus" level (`2(1 + Σ y)/2^k`, threshold `0.46 N`). -/
def plusFail (N : ℕ) (F' : Finset (State N)) (k : ℕ) : Set (Param N) :=
  {w | (23 / 50 : ℝ) * N < ∑ i, Real.log (max (2 * (1 + ∑ r ∈ F', clamp01 (w r i)) / 2 ^ k) 1)}

lemma plusFail_chernoff (F' : Finset (State N)) (k : ℕ) {β : ℝ}
    (hβ : ∫⁻ c, ENNReal.ofReal (max (2 * (1 + ∑ r ∈ F', clamp01 (c r)) / 2 ^ k) 1) ∂colLaw N ≤
      ENNReal.ofReal β) :
    cubeM N (plusFail N F' k) ≤ ENNReal.ofReal (Real.exp (-((23 / 50 : ℝ) * N)) * β ^ N) := by
  set A : (State N → ℝ) → ℝ := fun c => 2 * (1 + ∑ r ∈ F', clamp01 (c r)) / 2 ^ k with hA
  have hAm : Measurable A := by
    simp only [hA]
    exact ((measurable_const.add (Finset.measurable_sum _ fun r _ =>
      clamp01_measurable.comp (measurable_pi_apply r))).const_mul _).div_const _
  have hF : ∀ i : Fin N, Measurable fun c : State N → ℝ => -Real.log (max (A c) 1) :=
    fun _ => (Real.measurable_log.comp (hAm.max measurable_const)).neg
  have h := cubeM_chernoff_col_sum (fun _ c => -Real.log (max (A c) 1)) hF (a := -((23 / 50 : ℝ) * N))
    (t := 1) zero_le_one
  have hsub : plusFail N F' k ⊆ {w | ∑ i, (fun _ c => -Real.log (max (A c) 1)) i (fun r => w r i) ≤
      -((23 / 50 : ℝ) * N)} := by
    intro w hw
    simp only [plusFail, Set.mem_setOf_eq] at hw ⊢
    rw [Finset.sum_neg_distrib]; linarith
  refine (measure_mono hsub).trans (h.trans ?_)
  have hcol : ∀ i : Fin N, ∫⁻ c, ENNReal.ofReal (Real.exp (-1 * (fun _ c => -Real.log (max (A c) 1)) i c))
      ∂colLaw N ≤ ENNReal.ofReal β := by
    intro i
    refine le_trans (le_of_eq ?_) hβ
    refine lintegral_congr fun c => ?_
    congr 1
    simp only [neg_mul, one_mul, neg_neg]
    exact Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    push Not at hneg
    have : ENNReal.ofReal β = 0 := ENNReal.ofReal_of_nonpos hneg.le
    rw [this] at hβ
    have hpos : (0 : ENNReal) < ∫⁻ c, ENNReal.ofReal (max (A c) 1) ∂colLaw N := by
      haveI := colLaw_isProb (N := N)
      calc (0 : ENNReal) < ∫⁻ _c, (1 : ENNReal) ∂colLaw N := by simp
        _ ≤ _ := lintegral_mono fun c => by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    exact absurd hβ (not_le.2 hpos)
  calc ENNReal.ofReal (Real.exp (1 * -((23 / 50 : ℝ) * N))) *
        ∏ i, ∫⁻ c, ENNReal.ofReal (Real.exp (-1 * (fun _ c => -Real.log (max (A c) 1)) i c)) ∂colLaw N
      ≤ ENNReal.ofReal (Real.exp (1 * -((23 / 50 : ℝ) * N))) * ∏ _i : Fin N, ENNReal.ofReal β := by
        gcongr with i; exact hcol i
    _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hβ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, one_mul]

lemma exp_one_bounds : (2718 / 1000 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 27183 / 10000 := by
  have h1 := Real.exp_one_gt_d9; have h2 := Real.exp_one_lt_d9
  constructor <;> norm_num at * <;> linarith

/-- `e^{0.428125} ≥ 1.5196`. -/
lemma exp_rate_ge : (15196 / 10000 : ℝ) ≤ Real.exp (23 / 50 - 1 / 32) := by
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 23 / 50 - 1 / 32 by norm_num)
  nlinarith

lemma col_beta_nonneg {F' : Finset (State N)} {k : ℕ} {β : ℝ}
    (hβ : ∫⁻ c, ENNReal.ofReal (max (2 * (1 + ∑ r ∈ F', clamp01 (c r)) / 2 ^ k) 1) ∂colLaw N ≤
      ENNReal.ofReal β) : 0 ≤ β := by
  by_contra hneg
  push Not at hneg
  have : ENNReal.ofReal β = 0 := ENNReal.ofReal_of_nonpos hneg.le
  rw [this] at hβ
  haveI := colLaw_isProb (N := N)
  have hpos : (0 : ENNReal) < ∫⁻ c, ENNReal.ofReal (max (2 * (1 + ∑ r ∈ F', clamp01 (c r)) / 2 ^ k) 1)
      ∂colLaw N :=
    calc (0 : ENNReal) < ∫⁻ _c, (1 : ENNReal) ∂colLaw N := by simp
      _ ≤ _ := lintegral_mono fun c => by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  exact absurd hβ (not_le.2 hpos)

lemma q_bound2 : 0 ≤ (Real.exp 2 - 1) / 2 * Real.exp (-2) ∧ (Real.exp 2 - 1) / 2 * Real.exp (-2) ≤ 4324 / 10000 := by
  obtain ⟨he1, he2⟩ := exp_one_bounds
  have hE2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hm2 : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; simp
  have h1 := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.exp_pos (-2)
  refine ⟨mul_nonneg (div_nonneg (by linarith) (by norm_num)) hp.le, ?_⟩
  have hlt : Real.exp 2 < 7.39 := by rw [hE2]; nlinarith
  have hm : (1 : ℝ) / 7.39 ≤ Real.exp (-2) := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  have e : (Real.exp 2 - 1) / 2 * Real.exp (-2) = (1 - Real.exp (-2)) / 2 := by
    field_simp; nlinarith
  rw [e]; linarith

/-- **The failure probability of the subcube "plus" level**, `k ∈ {1, 2, 3}`. -/
theorem plusFail_le (F' : Finset (State N)) (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hcard : F'.card = 2 ^ k - 1) :
    cubeM N (plusFail N F' k) ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 32)) := by
  obtain ⟨he1, he2⟩ := exp_one_bounds
  have hr := exp_rate_ge
  have key : ∃ β : ℝ, β ≤ Real.exp (23 / 50 - 1 / 32) ∧
      ∫⁻ c, ENNReal.ofReal (max (2 * (1 + ∑ r ∈ F', clamp01 (c r)) / 2 ^ k) 1) ∂colLaw N ≤ ENNReal.ofReal β := by
    interval_cases k
    · -- k = 1, one row, μ = 10
      have hc : F'.card = 1 := by simp [hcard]
      refine ⟨_, ?_, col_maxPlus_le (N := N) F' 1 (μ := 10) (by norm_num)⟩
      rw [hc, show (2 : ℝ) * 10 / 2 ^ 1 = 10 by norm_num, show (10 : ℝ) - 10 = 0 by norm_num, Real.exp_zero]
      simp only [pow_one]
      have h10 : Real.exp 10 * Real.exp (-10) = 1 := by rw [← Real.exp_add]; simp
      have hq : (Real.exp 10 - 1) / 10 * Real.exp (-10) ≤ 1 / 10 := by
        have := Real.exp_pos (-10)
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by norm_num)]; nlinarith
      have hq0 : 0 ≤ (Real.exp 10 - 1) / 10 * Real.exp (-10) := by
        have := Real.one_le_exp (show (0 : ℝ) ≤ 10 by norm_num)
        exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (Real.exp_pos _).le
      have : 1 * ((Real.exp 10 - 1) / 10 * Real.exp (-10)) / (Real.exp 1 * 10) ≤ 1 / 100 / 2.718 := by
        rw [one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      push_cast
      linarith
    · -- k = 2, three rows, μ = 4
      have hc : F'.card = 3 := by simp [hcard]
      refine ⟨_, ?_, col_maxPlus_le (N := N) F' 2 (μ := 4) (by norm_num)⟩
      obtain ⟨hq0, hq1⟩ := q_bound2
      rw [hc, show (2 : ℝ) * 4 / 2 ^ 2 = 2 by norm_num, show (4 : ℝ) - 2 = 2 by norm_num]
      set q := (Real.exp 2 - 1) / 2 * Real.exp (-2) with hq
      have hE2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have hq3 : q ^ 3 ≤ (4324 / 10000) ^ 3 := pow_le_pow_left₀ hq0 hq1 3
      have e : Real.exp 2 * q ^ 3 / (Real.exp 1 * 4) = Real.exp 1 * q ^ 3 / 4 := by
        rw [hE2]; field_simp
      rw [e]
      have : Real.exp 1 * q ^ 3 ≤ (27183 / 10000) * (4324 / 10000) ^ 3 :=
        mul_le_mul he2.le hq3 (pow_nonneg hq0 3) (by norm_num)
      push_cast
      nlinarith
    · -- k = 3, seven rows, μ = 8
      have hc : F'.card = 7 := by simp [hcard]
      refine ⟨_, ?_, col_maxPlus_le (N := N) F' 3 (μ := 8) (by norm_num)⟩
      obtain ⟨hq0, hq1⟩ := q_bound2
      rw [hc, show (2 : ℝ) * 8 / 2 ^ 3 = 2 by norm_num, show (8 : ℝ) - 2 = 6 by norm_num]
      set q := (Real.exp 2 - 1) / 2 * Real.exp (-2) with hq
      have hE6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      have hq7 : q ^ 7 ≤ (4324 / 10000) ^ 7 := pow_le_pow_left₀ hq0 hq1 7
      have h5 : Real.exp 1 ^ 5 ≤ (27183 / 10000) ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le he2.le 5
      have e : Real.exp 6 * q ^ 7 / (Real.exp 1 * 8) = Real.exp 1 ^ 5 * q ^ 7 / 8 := by
        rw [hE6]; field_simp
      rw [e]
      have : Real.exp 1 ^ 5 * q ^ 7 ≤ (27183 / 10000) ^ 5 * (4324 / 10000) ^ 7 :=
        mul_le_mul h5 hq7 (pow_nonneg hq0 7) (by positivity)
      push_cast
      nlinarith
  obtain ⟨β, hβ, hcol⟩ := key
  have hβ0 := col_beta_nonneg hcol
  refine (plusFail_chernoff F' k hcol).trans (ENNReal.ofReal_le_ofReal ?_)
  calc Real.exp (-((23 / 50 : ℝ) * N)) * β ^ N ≤ Real.exp (-((23 / 50 : ℝ) * N)) * Real.exp (23 / 50 - 1 / 32) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ0 hβ N) (Real.exp_pos _).le
    _ = Real.exp (-(N : ℝ) / 32) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

/-! ### Joint bounds by independence -/

lemma card_agree_erase (K' : Finset (Fin N)) (t : State N) :
    ((agree K'ᶜ t).erase t).card = 2 ^ K'.card - 1 := by
  have ht : t ∈ agree K'ᶜ t := by rw [mem_agree]; intro j _; rfl
  rw [card_erase_of_mem ht, card_agree, card_compl, Fintype.card_fin]
  congr 2
  have := K'.card_le_univ; simp only [Fintype.card_fin] at this
  omega

/-- The plus-level failure reads only the rows of `F'`. -/
lemma plusFail_congr {F' : Finset (State N)} {k : ℕ} {w w' : Param N} (h : ∀ q ∈ F', w q = w' q)
    (hw : w ∈ plusFail N F' k) : w' ∈ plusFail N F' k := by
  simp only [plusFail, Set.mem_setOf_eq] at hw ⊢
  have : ∀ i, ∑ r ∈ F', clamp01 (w' r i) = ∑ r ∈ F', clamp01 (w r i) := fun i =>
    Finset.sum_congr rfl fun r hr => by rw [h r hr]
  simp_rw [this]; exact hw

/-- **Generic joint bound**: the regime event and a union of plus-level failures on row sets avoiding the rows
read by the regime event. -/
theorem joint_plus (hN7 : 7 ≤ N) (s r0 : State N) (x : Fin N) (σ : XSide) (hfar : N ≤ 3 * ham r0 s)
    (Ks : Finset (Finset (Fin N))) (t : Finset (Fin N) → State N)
    (hK : ∀ K' ∈ Ks, 1 ≤ K'.card ∧ K'.card ≤ 3)
    (hrows : ∀ K' ∈ Ks, r0 ∉ (agree K'ᶜ (t K')).erase (t K') ∧ s ∉ (agree K'ᶜ (t K')).erase (t K') ∧
      spRow s r0 x σ ∉ (agree K'ᶜ (t K')).erase (t K')) :
    cubeM N (⋃ K' ∈ Ks, {w | RegEvX N s r0 x σ w} ∩ plusFail N ((agree K'ᶜ (t K')).erase (t K')) K'.card) ≤
      ENNReal.ofReal (Ks.card * (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
        Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) * Real.exp (-(N : ℝ) / 32))) := by
  set B := 61 * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ K' ∈ Ks, cubeM N ({w | RegEvX N s r0 x σ w} ∩
      plusFail N ((agree K'ᶜ (t K')).erase (t K')) K'.card) ≤ ENNReal.ofReal (B * Real.exp (-(N : ℝ) / 32)) := by
    intro K' hK'
    obtain ⟨h1, h2, h3⟩ := hrows K' hK'
    rw [cubeM_inter_indep ((agree K'ᶜ (t K')).erase (t K')) _ _ ?_ ?_]
    · rw [ENNReal.ofReal_mul hB0]
      exact mul_le_mul' (regEvX_far_le hN7 s r0 x σ hfar)
        (plusFail_le _ K'.card (hK K' hK').1 (hK K' hK').2 (card_agree_erase K' (t K')))
    · intro w w' hq hw
      exact (regEvX_congr (hq r0 h1) (hq s h2) (hq _ h3)).1 hw
    · intro w w' hq hw
      exact plusFail_congr hq hw
  calc cubeM N (⋃ K' ∈ Ks, {w | RegEvX N s r0 x σ w} ∩ plusFail N ((agree K'ᶜ (t K')).erase (t K')) K'.card)
      ≤ ∑ K' ∈ Ks, cubeM N ({w | RegEvX N s r0 x σ w} ∩
          plusFail N ((agree K'ᶜ (t K')).erase (t K')) K'.card) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _K' ∈ Ks, ENNReal.ofReal (B * Real.exp (-(N : ℝ) / 32)) := sum_le_sum hterm
    _ = _ := by
        rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

/-- The subsets of size `1..3`. -/
noncomputable def subs3 (N : ℕ) : Finset (Finset (Fin N)) :=
  (univ : Finset (Finset (Fin N))).filter fun K' => 1 ≤ K'.card ∧ K'.card ≤ 3

lemma card_subs3 : ((subs3 N).card : ℝ) ≤ 3 * ((N : ℝ) + 1) ^ 3 := by
  have hsub : subs3 N ⊆ (univ.powersetCard 1) ∪ (univ.powersetCard 2) ∪ (univ.powersetCard 3) := by
    intro K' hK'
    simp only [subs3, mem_filter, mem_univ, true_and] at hK'
    simp only [mem_union, mem_powersetCard, subset_univ, true_and]
    omega
  have h := (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  simp only [card_powersetCard, card_univ, Fintype.card_fin] at h
  have h1 : (N.choose 1 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 := by
    have := Nat.choose_le_pow N 1
    have h' : ((N.choose 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 1 := by exact_mod_cast (this.trans (by simp))
    have : (N : ℝ) ^ 1 ≤ ((N : ℝ) + 1) ^ 3 := by
      rw [pow_one]; nlinarith [sq_nonneg ((N : ℝ) + 1), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    linarith
  have h2 : (N.choose 2 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 := by
    have h' : ((N.choose 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast (Nat.choose_le_pow N 2)
    have : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 3 := by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    linarith
  have h3 : (N.choose 3 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 := by
    have h' : ((N.choose 3 : ℕ) : ℝ) ≤ (N : ℝ) ^ 3 := by
      exact_mod_cast (Nat.choose_le_pow N 3)
    have : (N : ℝ) ^ 3 ≤ ((N : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg N) (by linarith) 3
    linarith
  have hcast : ((subs3 N).card : ℝ) ≤ (N.choose 1 : ℝ) + (N.choose 2 : ℝ) + (N.choose 3 : ℝ) := by
    exact_mod_cast h
  linarith

/-- Absorption of the joint-by-independence bound. -/
lemma joint_plus_absorb : ∀ᶠ N : ℕ in atTop, 3 * ((N : ℝ) + 1) ^ 3 * (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
    Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) * Real.exp (-(N : ℝ) / 32)) ≤
      Real.exp (-(RJ * N)) / 2 ^ N := by
  have hab := poly_absorb (3 * 61) 3 (δ := (rsR0 : ℝ) + 1 / 32 - RJ) (by unfold RJ rsR0; norm_num)
  filter_upwards [hab] with N hab
  have hsl := rs_slack_le N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hexp : Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-(N : ℝ) / 32) =
      Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e : 3 * ((N : ℝ) + 1) ^ 3 * (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
      Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) * Real.exp (-(N : ℝ) / 32)) =
      (3 * 61 * ((N : ℝ) + 1) ^ 3 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N))) / 2 ^ N := by
    rw [← hexp]; ring
  rw [e, div_le_div_iff_of_pos_right h2N]
  have hk : 3 * 61 * ((N : ℝ) + 1) ^ 3 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
      Real.exp ((((rsR0 : ℝ) + 1 / 32 - RJ)) * N) :=
    le_trans (by gcongr) hab
  have hy : Real.exp ((((rsR0 : ℝ) + 1 / 32 - RJ)) * N) *
      Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) = 1 := by rw [← Real.exp_add]; simp
  calc (3 * 61 * ((N : ℝ) + 1) ^ 3 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N)))
      ≤ Real.exp ((((rsR0 : ℝ) + 1 / 32 - RJ)) * N) *
          (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N))) := by gcongr
    _ = Real.exp (-(RJ * N)) := by rw [← mul_assoc, hy, one_mul]

/-- **`joint_nuTc`, PROVED** (independence of the subcube rows around `r0`). -/
theorem joint_nuTcF : JointBound P0NuTc := by
  filter_upwards [joint_plus_absorb, eventually_ge_atTop 15] with N hab hN s r0 x σ hfar
  cases σ with
  | cause =>
    have : {w : Param N | RegEvX N s r0 x .cause w ∧ ¬ P0NuTc N s r0 w x .cause} = ∅ := by
      ext w; simp [P0NuTc]
    rw [this, measure_empty]; exact zero_le
  | effect =>
    have hsub : {w : Param N | RegEvX N s r0 x .effect w ∧ ¬ P0NuTc N s r0 w x .effect} ⊆
        ⋃ K' ∈ subs3 N, {w | RegEvX N s r0 x .effect w} ∩
          plusFail N ((agree K'ᶜ ((fun _ => r0) K')).erase ((fun _ => r0) K')) K'.card := by
      rintro w ⟨hreg, hn⟩
      simp only [P0NuTc, forall_const, not_forall, not_le, exists_prop] at hn
      obtain ⟨K', hne, hc, hlt⟩ := hn
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      refine ⟨K', ?_, hreg, ?_⟩
      · simp only [subs3, mem_filter, mem_univ, true_and]; exact ⟨hne.card_pos, hc⟩
      · have e2 : ∀ i, 2 * b1CutMeanPlus w r0 K' i =
            2 * (1 + ∑ r ∈ (agree K'ᶜ r0).erase r0, clamp01 (w r i)) / 2 ^ K'.card := fun i => by
          unfold b1CutMeanPlus; ring
        simp only [e2] at hlt
        exact hlt
    refine (measure_mono hsub).trans ((joint_plus (by omega) s r0 x .effect hfar (subs3 N) (fun _ => r0)
      (fun K' hK' => by simp only [subs3, mem_filter, mem_univ, true_and] at hK'; exact hK') ?_).trans ?_)
    · intro K' hK'
      simp only [subs3, mem_filter, mem_univ, true_and] at hK'
      refine ⟨fun h => (mem_erase.1 h).1 rfl, fun h => ?_, fun h => ?_⟩
      · have h1 := ham_le_card_of_mem_agree (mem_erase.1 h).2
        rw [ham_comm] at h1; omega
      · have h1 := ham_le_card_of_mem_agree (mem_erase.1 h).2
        simp only [spRow] at h1
        have t1 := ham_triangle r0 (flipAt x s) s
        have t2 := ham_flipAt_le_one x s
        rw [ham_comm] at h1; omega
    · refine ENNReal.ofReal_le_ofReal (le_trans ?_ hab)
      gcongr
      exact card_subs3

/-! ### X5: the stated field is false; the corrected field (`x ∉ K'`) -/

/-- **`P0X5` fails on every cause-regime configuration** (for `N` large): at `K' = {x}` the plus mean of the
subcube through `r0^x` is `(1 + y_{r0,i})/2`, and the tilt `Σ -log y_{r0,i} ≤ x0 N + slT` gives
`Σ log(1 + y_{r0,i}) ≥ N log 2 - (x0 N + slT)/2 > 0.46 N` (AM-GM `log(1+y) ≥ log 2 + (log y)/2`) as soon as
all entries of row `r0` are positive.  Hence `JointBound P0X5` would force `P(RegEvX cause) ≤ e^{-RJ N}/2^N`,
contradicting the regime lower bound (`R* ≤ 1.008144 < RJ`). -/
theorem x5_fails_on_regime (hN : 1 ≤ N) (s r0 : State N) (x : Fin N) (w : Param N)
    (hpos : ∀ i, 0 < clamp01 (w r0 i)) (hT : XW w r0 ≤ x0 * N + slT N)
    (hbig : x0 * N + slT N < (2 * Real.log 2 - 23 / 25) * N) :
    ¬ ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 →
      ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ) := by
  intro h
  have h1 := h {x} (Finset.singleton_nonempty x) (by simp)
  have hag : (agree ({x} : Finset (Fin N))ᶜ (flipAt x r0)).erase (flipAt x r0) = {r0} := by
    ext q
    simp only [mem_erase, mem_agree, mem_compl, mem_singleton]
    constructor
    · rintro ⟨hne, hq⟩
      funext j
      by_cases hj : j = x
      · subst hj
        by_contra hc
        apply hne; funext j'
        by_cases hj' : j' = j
        · subst hj'; simp only [flipAt, Function.update_self]
          cases hqj : q j' <;> cases hrj : r0 j' <;> simp_all
        · rw [hq j' hj']
      · rw [hq j hj]; simp [flipAt, Function.update_of_ne hj]
    · rintro rfl
      refine ⟨(flipAt_ne x q).symm, fun j hj => ?_⟩
      simp [flipAt, Function.update_of_ne hj]
  have e : ∀ i, 2 * b1CutMeanPlus w (flipAt x r0) {x} i = 1 + clamp01 (w r0 i) := by
    intro i; unfold b1CutMeanPlus; rw [hag]; simp; ring
  simp only [e] at h1
  -- AM-GM: log(1+y) ≥ log 2 + (log y)/2
  have hamgm : ∀ i, Real.log 2 + Real.log (clamp01 (w r0 i)) / 2 ≤
      Real.log (max (1 + clamp01 (w r0 i)) 1) := by
    intro i
    have hy := hpos i
    have hy1 := clamp01_le_one (w r0 i)
    rw [max_eq_left (by linarith)]
    have : Real.log 2 + Real.log (clamp01 (w r0 i)) / 2 = Real.log (2 * Real.sqrt (clamp01 (w r0 i))) := by
      rw [Real.log_mul (by norm_num) (Real.sqrt_pos.2 hy).ne', Real.log_sqrt hy.le]
    rw [this]
    apply Real.log_le_log (by positivity)
    nlinarith [Real.sq_sqrt hy.le, Real.sqrt_nonneg (clamp01 (w r0 i)), sq_nonneg (Real.sqrt (clamp01 (w r0 i)) - 1)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ univ) => hamgm i
  rw [Finset.sum_add_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div] at hsum
  have hX : XW w r0 = ∑ i, -Real.log (clamp01 (w r0 i)) := rfl
  rw [Finset.sum_neg_distrib] at hX
  linarith

/-- The corrected X5 field: the subcubes through `r0^x` that do not contain `r0` (`x ∉ K'`). -/
def P0X5F (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .cause → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
    ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ)

/-- **Joint bound for the corrected X5 field, PROVED.** -/
theorem joint_x5F : JointBound P0X5F := by
  filter_upwards [joint_plus_absorb, eventually_ge_atTop 15] with N hab hN s r0 x σ hfar
  cases σ with
  | effect =>
    have : {w : Param N | RegEvX N s r0 x .effect w ∧ ¬ P0X5F N s r0 w x .effect} = ∅ := by
      ext w; simp [P0X5F]
    rw [this, measure_empty]; exact zero_le
  | cause =>
    set Ks := (subs3 N).filter fun K' => x ∉ K' with hKs
    have hsub : {w : Param N | RegEvX N s r0 x .cause w ∧ ¬ P0X5F N s r0 w x .cause} ⊆
        ⋃ K' ∈ Ks, {w | RegEvX N s r0 x .cause w} ∩
          plusFail N ((agree K'ᶜ ((fun _ => flipAt x r0) K')).erase ((fun _ => flipAt x r0) K')) K'.card := by
      rintro w ⟨hreg, hn⟩
      simp only [P0X5F, forall_const, not_forall, not_le, exists_prop] at hn
      obtain ⟨K', hne, hc, hxK, hlt⟩ := hn
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      refine ⟨K', ?_, hreg, ?_⟩
      · simp only [hKs, subs3, mem_filter, mem_univ, true_and]; exact ⟨⟨hne.card_pos, hc⟩, hxK⟩
      · have e2 : ∀ i, 2 * b1CutMeanPlus w (flipAt x r0) K' i =
            2 * (1 + ∑ r ∈ (agree K'ᶜ (flipAt x r0)).erase (flipAt x r0), clamp01 (w r i)) / 2 ^ K'.card :=
          fun i => by unfold b1CutMeanPlus; ring
        simp only [e2] at hlt
        exact hlt
    refine (measure_mono hsub).trans ((joint_plus (by omega) s r0 x .cause hfar Ks (fun _ => flipAt x r0)
      (fun K' hK' => by
        simp only [hKs, subs3, mem_filter, mem_univ, true_and] at hK'; exact hK'.1) ?_).trans ?_)
    · intro K' hK'
      simp only [hKs, subs3, mem_filter, mem_univ, true_and] at hK'
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have h1 := (mem_erase.1 h).2
        rw [mem_agree] at h1
        have := h1 x (by simpa using hK'.2)
        simp [flipAt] at this
      · have h1 := ham_le_card_of_mem_agree (mem_erase.1 h).2
        have t1 := ham_triangle r0 (flipAt x r0) s
        have t2 := ham_flipAt_le_one x r0
        rw [ham_comm (flipAt x r0) r0] at t2
        rw [ham_comm] at h1; omega
      · simp only [spRow] at h; exact (mem_erase.1 h).1 rfl
    · refine ENNReal.ofReal_le_ofReal (le_trans ?_ hab)
      gcongr
      exact (Nat.cast_le.2 (card_filter_le _ _)).trans card_subs3

/-! ### nuS: all subcubes except `K' = {x}` on the effect side -/

/-- A generic column failure event `Σ_i log max(A(column i), 1) > 0.46 N`. -/
lemma colFail_chernoff (A : (State N → ℝ) → ℝ) (hA : Measurable A) {β : ℝ}
    (hβ : ∫⁻ c, ENNReal.ofReal (max (A c) 1) ∂colLaw N ≤ ENNReal.ofReal β) (hβ0 : 0 ≤ β) :
    cubeM N {w | (23 / 50 : ℝ) * N < ∑ i, Real.log (max (A (fun r => w r i)) 1)} ≤
      ENNReal.ofReal (Real.exp (-((23 / 50 : ℝ) * N)) * β ^ N) := by
  have hF : ∀ i : Fin N, Measurable fun c : State N → ℝ => -Real.log (max (A c) 1) :=
    fun _ => (Real.measurable_log.comp (hA.max measurable_const)).neg
  have h := cubeM_chernoff_col_sum (fun _ c => -Real.log (max (A c) 1)) hF (a := -((23 / 50 : ℝ) * N))
    (t := 1) zero_le_one
  have hsub : {w : Param N | (23 / 50 : ℝ) * N < ∑ i, Real.log (max (A (fun r => w r i)) 1)} ⊆
      {w | ∑ i, (fun _ c => -Real.log (max (A c) 1)) i (fun r => w r i) ≤ -((23 / 50 : ℝ) * N)} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    rw [Finset.sum_neg_distrib]; linarith
  refine (measure_mono hsub).trans (h.trans ?_)
  have hcol : ∀ i : Fin N, ∫⁻ c, ENNReal.ofReal (Real.exp (-1 * (fun _ c => -Real.log (max (A c) 1)) i c))
      ∂colLaw N ≤ ENNReal.ofReal β := by
    intro i
    refine le_trans (le_of_eq ?_) hβ
    refine lintegral_congr fun c => ?_
    congr 1
    simp only [neg_mul, one_mul, neg_neg]
    exact Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))
  calc ENNReal.ofReal (Real.exp (1 * -((23 / 50 : ℝ) * N))) *
        ∏ i, ∫⁻ c, ENNReal.ofReal (Real.exp (-1 * (fun _ c => -Real.log (max (A c) 1)) i c)) ∂colLaw N
      ≤ ENNReal.ofReal (Real.exp (1 * -((23 / 50 : ℝ) * N))) * ∏ _i : Fin N, ENNReal.ofReal β := by
        gcongr with i; exact hcol i
    _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hβ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, one_mul]

/-- The two-row level with offset `2`: `(2 + y + y')/2 ≥ 1`. -/
def plus2Fail (N : ℕ) (F'' : Finset (State N)) : Set (Param N) :=
  {w | (23 / 50 : ℝ) * N < ∑ i, Real.log (max ((2 + ∑ r ∈ F'', clamp01 (w r i)) / 2) 1)}

theorem plus2Fail_le (F'' : Finset (State N)) (hc : F''.card = 2) :
    cubeM N (plus2Fail N F'') ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 32)) := by
  haveI := colLaw_isProb (N := N)
  set A : (State N → ℝ) → ℝ := fun c => (2 + ∑ r ∈ F'', clamp01 (c r)) / 2 with hA
  have hAm : Measurable A := by
    simp only [hA]
    exact (measurable_const.add (Finset.measurable_sum _ fun r _ =>
      clamp01_measurable.comp (measurable_pi_apply r))).div_const _
  have hm1 : ∀ r, Measurable fun c : State N → ℝ => ENNReal.ofReal (1 / 2 * clamp01 (c r)) :=
    fun r => ENNReal.measurable_ofReal.comp (measurable_const.mul (clamp01_measurable.comp (measurable_pi_apply r)))
  have hlin : ∫⁻ u, ENNReal.ofReal (1 / 2 * clamp01 u) ∂unif = ENNReal.ofReal (1 / 4) := by
    have := lintegral_unif_pow 1
    simp only [pow_one] at this
    rw [show (fun u : ℝ => ENNReal.ofReal (1 / 2 * clamp01 u)) =
        fun u => ENNReal.ofReal (1 / 2) * ENNReal.ofReal (clamp01 u) from
      funext fun u => ENNReal.ofReal_mul (by norm_num),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, this, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hβ : ∫⁻ c, ENNReal.ofReal (max (A c) 1) ∂colLaw N ≤ ENNReal.ofReal (3 / 2) := by
    have hpt : ∀ c, ENNReal.ofReal (max (A c) 1) =
        ENNReal.ofReal 1 + ∑ r ∈ F'', ENNReal.ofReal (1 / 2 * clamp01 (c r)) := by
      intro c
      have hS : 0 ≤ ∑ r ∈ F'', clamp01 (c r) := Finset.sum_nonneg fun r _ => clamp01_nonneg _
      rw [max_eq_left (by simp only [hA]; linarith), ← ENNReal.ofReal_sum_of_nonneg
        (fun r _ => mul_nonneg (by norm_num) (clamp01_nonneg _)), ← ENNReal.ofReal_add (by norm_num)
        (Finset.sum_nonneg fun r _ => mul_nonneg (by norm_num) (clamp01_nonneg _))]
      congr 1; simp only [hA]; rw [← Finset.mul_sum]; ring
    simp_rw [hpt]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_finsetSum _ fun r _ => hm1 r]
    rw [Finset.sum_congr rfl fun r _ => by
      rw [lintegral_colLaw_eval (f := fun u => ENNReal.ofReal (1 / 2 * clamp01 u)) r
        (ENNReal.measurable_ofReal.comp (measurable_const.mul clamp01_measurable)), hlin]]
    rw [sum_const, hc, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have h := colFail_chernoff A hAm hβ (by norm_num)
  refine (le_of_eq_of_le (by rfl) h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hr := exp_rate_ge
  calc Real.exp (-((23 / 50 : ℝ) * N)) * (3 / 2) ^ N ≤ Real.exp (-((23 / 50 : ℝ) * N)) * Real.exp (23 / 50 - 1 / 32) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by linarith) N) (Real.exp_pos _).le
    _ = Real.exp (-(N : ℝ) / 32) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

lemma plus2Fail_congr {F'' : Finset (State N)} {w w' : Param N} (h : ∀ q ∈ F'', w q = w' q)
    (hw : w ∈ plus2Fail N F'') : w' ∈ plus2Fail N F'' := by
  simp only [plus2Fail, Set.mem_setOf_eq] at hw ⊢
  have : ∀ i, ∑ r ∈ F'', clamp01 (w' r i) = ∑ r ∈ F'', clamp01 (w r i) := fun i =>
    Finset.sum_congr rfl fun r hr => by rw [h r hr]
  simp_rw [this]; exact hw

/-- **The remaining nuS sub-leaf** (effect side, `K' = {x}`): W7 "nuS through `s^x`" (float +0.060). -/
def NuSxStmt : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    cubeM N {w | RegEvX N s r0 x .effect w ∧
      (23 / 50 : ℝ) * N < ∑ i, Real.log (max (clamp01 (w s i) + clamp01 (w (flipAt x s) i)) 1)} ≤
      ENNReal.ofReal (Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N)

lemma joint_plus_absorb9 : ∀ᶠ N : ℕ in atTop, 9 * ((N : ℝ) + 1) ^ 3 * (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
    Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) * Real.exp (-(N : ℝ) / 32)) ≤
      Real.exp (-(RJ * N)) / 2 ^ N := by
  have hab := poly_absorb (9 * 61) 3 (δ := (rsR0 : ℝ) + 1 / 32 - RJ) (by unfold RJ rsR0; norm_num)
  filter_upwards [hab] with N hab
  have hsl := rs_slack_le N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hexp : Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-(N : ℝ) / 32) =
      Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e : 9 * ((N : ℝ) + 1) ^ 3 * (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
      Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) * Real.exp (-(N : ℝ) / 32)) =
      (9 * 61 * ((N : ℝ) + 1) ^ 3 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N))) / 2 ^ N := by
    rw [← hexp]; ring
  rw [e, div_le_div_iff_of_pos_right h2N]
  have hk : 9 * 61 * ((N : ℝ) + 1) ^ 3 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
      Real.exp ((((rsR0 : ℝ) + 1 / 32 - RJ)) * N) :=
    le_trans (by gcongr) hab
  have hy : Real.exp ((((rsR0 : ℝ) + 1 / 32 - RJ)) * N) *
      Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) = 1 := by rw [← Real.exp_add]; simp
  calc (9 * 61 * ((N : ℝ) + 1) ^ 3 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N)))
      ≤ Real.exp ((((rsR0 : ℝ) + 1 / 32 - RJ)) * N) *
          (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - RJ)) * N)) * Real.exp (-(RJ * N))) := by gcongr
    _ = Real.exp (-(RJ * N)) := by rw [← mul_assoc, hy, one_mul]

lemma exp_RJ2_le : ∀ᶠ N : ℕ in atTop, 3 * Real.exp (-((10109 / 10000 : ℝ) * N)) ≤ Real.exp (-(RJ * N)) := by
  have ht : Tendsto (fun N : ℕ => Real.exp (-((10109 / 10000 - RJ) * N))) atTop (𝓝 0) := by
    have hpos : 0 < (10109 / 10000 : ℝ) - RJ := by unfold RJ; norm_num
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop hpos
  filter_upwards [(ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)))] with N hN
  have e : Real.exp (-((10109 / 10000 : ℝ) * N)) = Real.exp (-((10109 / 10000 - RJ) * N)) * Real.exp (-(RJ * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have := Real.exp_pos (-(RJ * N))
  nlinarith

/-- **`joint_nuS` from the `K' = {x}` effect sub-leaf.** -/
theorem joint_nuS_of (hx : NuSxStmt) : JointBound P0NuS := by
  filter_upwards [hx, joint_plus_absorb9, exp_RJ2_le, eventually_ge_atTop 15] with N hx hab h3 hN s r0 x σ hfar
  set B := 61 * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) with hB
  have hB0 : 0 ≤ B := by positivity
  set E := Real.exp (-(N : ℝ) / 32) with hE
  -- the families
  set Ka := (subs3 N).filter fun K' => K'.card ≤ 2 ∧ (σ = .cause ∨ x ∉ K') with hKa
  set Kc := ((subs3 N).filter fun K' => K'.card = 2 ∧ σ = .effect ∧ x ∈ K') with hKc
  have hdom : ∀ (w : Param N) (K' : Finset (Fin N)) (i : Fin N),
      2 * b1CutMeanS w s r0 K' i ≤ 2 * (1 + ∑ r ∈ (agree K'ᶜ s).erase s, clamp01 (w r i)) / 2 ^ K'.card := by
    intro w K' i
    have hs : s ∈ agree K'ᶜ s := by rw [mem_agree]; intro j _; rfl
    unfold b1CutMeanS
    rw [← Finset.add_sum_erase _ _ hs]
    have := clamp01_le_one (w s i)
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hlogmono : ∀ {a b : ℝ}, a ≤ b → Real.log (max a 1) ≤ Real.log (max b 1) := fun h =>
    Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le_max h le_rfl)
  have hsub : {w : Param N | RegEvX N s r0 x σ w ∧ ¬ P0NuS N s r0 w x σ} ⊆
      (⋃ K' ∈ Ka, {w | RegEvX N s r0 x σ w} ∩
          plusFail N ((agree K'ᶜ ((fun _ => s) K')).erase ((fun _ => s) K')) K'.card) ∪
        (⋃ K' ∈ Kc, {w | RegEvX N s r0 x σ w} ∩ plus2Fail N (((agree K'ᶜ s).erase s).erase (flipAt x s))) ∪
        {w | RegEvX N s r0 x σ w ∧ σ = .effect ∧
          (23 / 50 : ℝ) * N < ∑ i, Real.log (max (clamp01 (w s i) + clamp01 (w (flipAt x s) i)) 1)} := by
    rintro w ⟨hreg, hn⟩
    simp only [P0NuS, not_forall, not_le, exists_prop] at hn
    obtain ⟨K', hne, hc, hlt⟩ := hn
    have hK1 : 1 ≤ K'.card := hne.card_pos
    by_cases hgood : σ = .cause ∨ x ∉ K'
    · left; left
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      refine ⟨K', ?_, hreg, ?_⟩
      · simp only [hKa, subs3, mem_filter, mem_univ, true_and]; exact ⟨⟨hK1, by omega⟩, hc, hgood⟩
      · simp only [plusFail, Set.mem_setOf_eq]
        exact lt_of_lt_of_le hlt (Finset.sum_le_sum fun i _ => hlogmono (hdom w K' i))
    · push Not at hgood
      obtain ⟨hσ, hxK⟩ := hgood
      have hσe : σ = .effect := by cases σ <;> simp_all
      rcases Nat.lt_or_ge K'.card 2 with h1 | h2
      · -- K' = {x}
        right
        have hKx : K' = {x} := by
          have : K'.card = 1 := by omega
          obtain ⟨a, ha⟩ := Finset.card_eq_one.1 this
          rw [ha] at hxK ⊢; simp at hxK; rw [hxK]
        refine ⟨hreg, hσe, ?_⟩
        have hag : agree ({x} : Finset (Fin N))ᶜ s = {s, flipAt x s} := by
          ext q
          simp only [mem_agree, mem_compl, mem_singleton, mem_insert]
          constructor
          · intro hq
            by_cases hqx : q x = s x
            · left; funext j; by_cases hj : j = x
              · subst hj; exact hqx
              · exact hq j hj
            · right; funext j; by_cases hj : j = x
              · subst hj; simp only [flipAt, Function.update_self]
                cases hq1 : q j <;> cases hs1 : s j <;> simp_all
              · rw [hq j hj]; simp [flipAt, Function.update_of_ne hj]
          · rintro (rfl | rfl) j hj
            · rfl
            · simp [flipAt, Function.update_of_ne hj]
        have e : ∀ i, 2 * b1CutMeanS w s r0 {x} i = clamp01 (w s i) + clamp01 (w (flipAt x s) i) := by
          intro i; unfold b1CutMeanS; rw [hag, Finset.sum_pair (flipAt_ne x s).symm]; simp; ring
        rw [hKx] at hlt; simp only [e] at hlt; exact hlt
      · -- |K'| = 2, x ∈ K'
        left; right
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
        refine ⟨K', ?_, hreg, ?_⟩
        · simp only [hKc, subs3, mem_filter, mem_univ, true_and]; exact ⟨⟨hK1, by omega⟩, by omega, hσe, hxK⟩
        · simp only [plus2Fail, Set.mem_setOf_eq]
          refine lt_of_lt_of_le hlt (Finset.sum_le_sum fun i _ => hlogmono ?_)
          have hs : s ∈ agree K'ᶜ s := by rw [mem_agree]; intro j _; rfl
          have hsx : flipAt x s ∈ (agree K'ᶜ s).erase s := by
            refine mem_erase.2 ⟨flipAt_ne x s, ?_⟩
            rw [mem_agree]; intro j hj
            have : j ≠ x := fun h => (mem_compl.1 hj) (h ▸ hxK)
            simp [flipAt, Function.update_of_ne this]
          have hc2 : K'.card = 2 := by omega
          unfold b1CutMeanS
          rw [← Finset.add_sum_erase _ _ hs, ← Finset.add_sum_erase _ _ hsx, hc2]
          have := clamp01_le_one (w s i)
          have := clamp01_le_one (w (flipAt x s) i)
          have e : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
          rw [e]; linarith
  have hAp : cubeM N (⋃ K' ∈ Ka, {w | RegEvX N s r0 x σ w} ∩
      plusFail N ((agree K'ᶜ ((fun _ => s) K')).erase ((fun _ => s) K')) K'.card) ≤
      ENNReal.ofReal (Ka.card * (B * E)) := by
    exact joint_plus (by omega) s r0 x σ hfar Ka (fun _ => s)
        (fun K' hK' => by simp only [hKa, subs3, mem_filter, mem_univ, true_and] at hK'; exact hK'.1) (by
          intro K' hK'
          simp only [hKa, subs3, mem_filter, mem_univ, true_and] at hK'
          refine ⟨fun h => ?_, fun h => (mem_erase.1 h).1 rfl, fun h => ?_⟩
          · have h1 := ham_le_card_of_mem_agree (mem_erase.1 h).2
            omega
          · rcases hK'.2.2 with hc | hx'
            · subst hc; simp only [spRow] at h
              have h1 := ham_le_card_of_mem_agree (mem_erase.1 h).2
              have t1 := ham_triangle r0 (flipAt x r0) s
              have t2 := ham_flipAt_le_one x r0
              rw [ham_comm (flipAt x r0) r0] at t2
              omega
            · cases σ
              · simp only [spRow] at h
                have h1 := ham_le_card_of_mem_agree (mem_erase.1 h).2
                have t1 := ham_triangle r0 (flipAt x r0) s
                have t2 := ham_flipAt_le_one x r0
                rw [ham_comm (flipAt x r0) r0] at t2
                omega
              · simp only [spRow] at h
                have h1 := (mem_erase.1 h).2
                rw [mem_agree] at h1
                have := h1 x (by simpa using hx')
                simp [flipAt] at this)
  have hCp : cubeM N (⋃ K' ∈ Kc, {w | RegEvX N s r0 x σ w} ∩
      plus2Fail N (((agree K'ᶜ s).erase s).erase (flipAt x s))) ≤ ENNReal.ofReal (Kc.card * (B * E)) := by
        calc cubeM N (⋃ K' ∈ Kc, {w | RegEvX N s r0 x σ w} ∩ plus2Fail N (((agree K'ᶜ s).erase s).erase (flipAt x s)))
        ≤ ∑ K' ∈ Kc, cubeM N ({w | RegEvX N s r0 x σ w} ∩
            plus2Fail N (((agree K'ᶜ s).erase s).erase (flipAt x s))) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _K' ∈ Kc, ENNReal.ofReal (B * E) := by
          refine sum_le_sum fun K' hK' => ?_
          simp only [hKc, subs3, mem_filter, mem_univ, true_and] at hK'
          obtain ⟨-, hc2, hσe, hxK⟩ := hK'
          have hs : s ∈ agree K'ᶜ s := by rw [mem_agree]; intro j _; rfl
          have hsx : flipAt x s ∈ (agree K'ᶜ s).erase s := by
            refine mem_erase.2 ⟨flipAt_ne x s, ?_⟩
            rw [mem_agree]; intro j hj
            have : j ≠ x := fun h => (mem_compl.1 hj) (h ▸ hxK)
            simp [flipAt, Function.update_of_ne this]
          have hcard : (((agree K'ᶜ s).erase s).erase (flipAt x s)).card = 2 := by
            rw [card_erase_of_mem hsx, card_agree_erase, hc2]; norm_num
          rw [cubeM_inter_indep (((agree K'ᶜ s).erase s).erase (flipAt x s)) _ _ ?_ ?_]
          · rw [ENNReal.ofReal_mul hB0]
            exact mul_le_mul' (regEvX_far_le (by omega) s r0 x σ hfar) (plus2Fail_le _ hcard)
          · intro w w' hq hw
            have hr0 : r0 ∉ ((agree K'ᶜ s).erase s).erase (flipAt x s) := fun h => by
              have h1 := ham_le_card_of_mem_agree (mem_erase.1 (mem_erase.1 h).2).2
              omega
            have hs' : s ∉ ((agree K'ᶜ s).erase s).erase (flipAt x s) := fun h =>
              (mem_erase.1 (mem_erase.1 h).2).1 rfl
            have hsp : spRow s r0 x σ ∉ ((agree K'ᶜ s).erase s).erase (flipAt x s) := by
              subst hσe; simp only [spRow]; exact fun h => (mem_erase.1 h).1 rfl
            exact (regEvX_congr (hq r0 hr0) (hq s hs') (hq _ hsp)).1 hw
          · intro w w' hq hw; exact plus2Fail_congr hq hw
      _ = ENNReal.ofReal (Kc.card * (B * E)) := by
          rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  have hXp : cubeM N {w | RegEvX N s r0 x σ w ∧ σ = .effect ∧
      (23 / 50 : ℝ) * N < ∑ i, Real.log (max (clamp01 (w s i) + clamp01 (w (flipAt x s) i)) 1)} ≤
      ENNReal.ofReal (Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N) := by
    by_cases hσ : σ = .effect
    · subst hσ
      refine (measure_mono ?_).trans (hx s r0 x hfar)
      rintro w ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · have : {w : Param N | RegEvX N s r0 x σ w ∧ σ = .effect ∧
          (23 / 50 : ℝ) * N < ∑ i, Real.log (max (clamp01 (w s i) + clamp01 (w (flipAt x s) i)) 1)} = ∅ := by
        ext w; simp [hσ]
      rw [this, measure_empty]; exact zero_le
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add ((measure_union_le _ _).trans
    (add_le_add hAp hCp)) hXp).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hKa : (Ka.card : ℝ) ≤ 3 * ((N : ℝ) + 1) ^ 3 := (Nat.cast_le.2 (card_filter_le _ _)).trans card_subs3
  have hKc : (Kc.card : ℝ) ≤ 3 * ((N : ℝ) + 1) ^ 3 := (Nat.cast_le.2 (card_filter_le _ _)).trans card_subs3
  have hBE : 0 ≤ B * E := by positivity
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hx3 : Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N ≤ Real.exp (-(RJ * N)) / 2 ^ N / 3 := by
    rw [div_div, div_le_div_iff₀ h2N (by positivity)]; nlinarith
  have : (Ka.card : ℝ) * (B * E) + Kc.card * (B * E) ≤ 2 * (Real.exp (-(RJ * N)) / 2 ^ N) / 3 := by
    have h9 : 9 * ((N : ℝ) + 1) ^ 3 * (B * E) ≤ Real.exp (-(RJ * N)) / 2 ^ N := by
      simpa [hB, hE, mul_assoc] using hab
    nlinarith [mul_le_mul_of_nonneg_right hKa hBE, mul_le_mul_of_nonneg_right hKc hBE]
  linarith

end Census
end IIT

#print axioms IIT.Census.joint_nuTcF
#print axioms IIT.Census.joint_x5F
#print axioms IIT.Census.joint_nuS_of
#print axioms IIT.Census.x5_fails_on_regime
