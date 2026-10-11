/-
Census, module D1' part 2 (Lemma RS, W9 §4.1): one regime-X cause cell inside A4's joint Chernoff template.

The cell event `CellEvX (r0, x, cause, c)` reads three distinct rows: `r0` (tilt and base entries), `r0^x` (the
near-copy row, through `lamX`) and `s` (the link). It is contained in the event of `joint_template_real` with
* `ell y = -log y` (tilt), bound `B = x0 N + slT N`;
* `ellU y = -log max(y, 1-y) - slT/N` (link, slack absorbed per unit);
* `g y u = min(log(2y/(y+u)), max 0 (log(y/c_m)) - 7 δ) - (slV + log 2)/N` (V-sum over all units; unit `x`'s own
  term is at most `log 2` since `c_m ≥ 1/2`);
* `W = {y | m_lo ≤ y}` (every base entry above `m_lo`; the conjunct `∃ j, y_j ≤ c_m` is dropped).
-/
import IIT.Census.B1DefsX
import IIT.Census.B1RegMGF
import IIT.Census.B1RegInt

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-- The per-unit V-term of the template. -/
noncomputable def gXev (N : ℕ) (c : ℚ × ℚ) (y u : ℝ) : ℝ :=
  min (Real.log (2 * clamp01 y / (clamp01 y + clamp01 u)))
      (max 0 (Real.log (clamp01 y / (c.2 : ℝ))) - 7 * deltaU N) - (slV N + Real.log 2) / N

/-- The link term of the template. -/
noncomputable def ellUX (N : ℕ) (y : ℝ) : ℝ := -Real.log (max (clamp01 y) (1 - clamp01 y)) - slT N / N

/-- **A cause cell inside the joint template event.** -/
lemma cellEvX_sub_template (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ)
    (hcm : (1 : ℝ) / 2 ≤ c.2) :
    {w : Param N | CellEvX N s r0 x .cause c w} ⊆
      {w | (∀ i, w ((fun _ : Fin N => r0) i) i ∈ {y : ℝ | (c.1 : ℝ) ≤ clamp01 y}) ∧
        ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ≤ x0 * N + slT N ∧
        ∑ i, ellUX N (w ((fun _ : Fin N => s) i) i) ≤
          ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, gXev N c (w ((fun _ : Fin N => r0) i) i) (w ((fun _ : Fin N => flipAt x r0) i) i) ≤ 0} := by
  rintro w ⟨h1, -, h3, h4, h5, -⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun i => h1 i, h3, ?_, ?_⟩
  · -- link
    have : ∑ i, ellUX N (w s i) = ∑ k, -Real.log (xE w s k) - slT N := by
      simp only [ellUX, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hNr.ne']
      rfl
    show ∑ i, ellUX N (w s i) ≤ ∑ i, -Real.log (clamp01 (w r0 i))
    rw [this]
    have hX : XW w r0 = ∑ i, -Real.log (clamp01 (w r0 i)) := rfl
    linarith
  · -- V-sum: unit x's own term is at most log 2
    set V : Fin N → ℝ := fun i => min (Real.log (2 * clamp01 (w r0 i) /
        (clamp01 (w r0 i) + clamp01 (w (flipAt x r0) i))))
        (max 0 (Real.log (clamp01 (w r0 i) / (c.2 : ℝ))) - 7 * deltaU N) with hVdef
    have hsum : ∑ i, gXev N c (w r0 i) (w (flipAt x r0) i) = ∑ i, V i - (slV N + Real.log 2) := by
      simp only [gXev, hVdef, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hNr.ne']
    have hVx : V x ≤ Real.log 2 := by
      have hδ : 0 ≤ deltaU N := by unfold deltaU; positivity
      have hc0 : (0 : ℝ) < c.2 := by linarith
      have hlog : Real.log (clamp01 (w r0 x) / (c.2 : ℝ)) ≤ Real.log 2 := by
        rcases (clamp01_nonneg (w r0 x)).eq_or_lt with h0 | hpos
        · rw [← h0, zero_div, Real.log_zero]; exact (Real.log_pos one_lt_two).le
        · exact Real.log_le_log (div_pos hpos hc0) (by
            rw [div_le_iff₀ hc0]; have := clamp01_le_one (w r0 x); linarith)
      have := min_le_right (Real.log (2 * clamp01 (w r0 x) /
        (clamp01 (w r0 x) + clamp01 (w (flipAt x r0) x))))
        (max 0 (Real.log (clamp01 (w r0 x) / (c.2 : ℝ))) - 7 * deltaU N)
      have h2 : max 0 (Real.log (clamp01 (w r0 x) / (c.2 : ℝ))) ≤ Real.log 2 :=
        max_le (Real.log_pos one_lt_two).le hlog
      simp only [hVdef]; linarith
    have hrest : ∑ i ∈ univ.erase x, V i ≤ slV N := h5
    show ∑ i, gXev N c (w r0 i) (w (flipAt x r0) i) ≤ 0
    rw [hsum, ← add_sum_erase _ _ (mem_univ x)]
    linarith

/-- **One cause cell, Chernoff bound** (rows `r0`, `r0^x`, `s` distinct). `J` and `Ex` are the per-unit
factors of `joint_template_real`; the numerical part bounds them from the certificate. -/
theorem cellEvX_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2)
    (hr0s : r0 ≠ s) (hr1s : flipAt x r0 ≠ s) (t lamU lam : ℝ) (ht : 0 ≤ t) (hlamU : 0 ≤ lamU)
    (hlam : 0 ≤ lam) {J Ex : ℝ} (hJ0 : 0 ≤ J) (hE0 : 0 ≤ Ex)
    (hJ : ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * gXev N c y u)) ∂unif ∂unif ≤ ENNReal.ofReal J)
    (hE : ∫⁻ y, ENNReal.ofReal (Real.exp (-lamU * ellUX N y)) ∂unif ≤ ENNReal.ofReal Ex) :
    cubeM N {w : Param N | CellEvX N s r0 x .cause c w} ≤
      ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * (J * Ex) ^ N) := by
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellU : Measurable (ellUX N) := by
    unfold ellUX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  have hg : Measurable fun p : ℝ × ℝ => gXev N c p.1 p.2 := by
    unfold gXev
    have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
    have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
    refine (Measurable.min ?_ ?_).sub_const _
    · exact Real.measurable_log.comp ((measurable_const.mul hy).div (hy.add hu))
    · exact (measurable_const.max (Real.measurable_log.comp (hy.div_const _))).sub_const _
  have hW : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ clamp01 y} :=
    measurableSet_le measurable_const clamp01_measurable
  refine (measure_mono (cellEvX_sub_template hN s r0 x c hcm)).trans ?_
  exact joint_template_real (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => hr0s) (fun _ => hr1s)
    (fun y => -Real.log (clamp01 y)) (ellUX N) (gXev N c) hell hellU hg _ hW
    (x0 * N + slT N) t lamU lam ht hlamU hlam hJ0 hE0 hJ hE

/-- **The inner factor of `J`**: for a base entry `y ∈ (0, 1]` and `λ ∈ ℕ`, the `unif`-expectation of
`exp(-λ gXev)` is at most `exp(λ(7δ + (slV + log 2)/N)) · gX λ c_m y`. -/
theorem inner_mgf_le (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {y : ℝ}
    (hy0 : 0 < clamp01 y) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        gX lam (c.2 : ℝ) (clamp01 y)) := by
  set Y := clamp01 y
  have hY1 : Y ≤ 1 := clamp01_le_one y
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hYc : Y ≤ 2 * (c.2 : ℝ) := by linarith
  set K := 7 * deltaU N + (slV N + Real.log 2) / N
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(lam : ℝ) * gXev N c y u) ≤
      Real.exp ((lam : ℝ) * K) * Real.exp (-(lam : ℝ) *
        min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2)))) := by
    intro u hu
    have hcu : clamp01 u = u := by
      unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]
    rw [← Real.exp_add, Real.exp_le_exp]
    unfold gXev
    rw [hcu]
    have hmin : min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2))) - 7 * deltaU N ≤
        min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2)) - 7 * deltaU N) := by
      have hδ : 0 ≤ deltaU N := by unfold deltaU; positivity
      rcases le_total (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2))) with h | h
      · rw [min_eq_left h]; exact le_min (by linarith) (by linarith)
      · rw [min_eq_right h]; exact le_min (by linarith) le_rfl
    have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
    simp only [K]
    nlinarith [mul_le_mul_of_nonneg_left hmin hl]
  calc ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂unif
      ≤ ∫⁻ u, ENNReal.ofReal (Real.exp ((lam : ℝ) * K)) * ENNReal.ofReal (Real.exp (-(lam : ℝ) *
          min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2))))) ∂unif := by
        unfold unif
        refine setLIntegral_mono' measurableSet_Icc fun u hu => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (hpt u hu)
    _ = ENNReal.ofReal (Real.exp ((lam : ℝ) * K)) * ENNReal.ofReal (gX lam (c.2 : ℝ) Y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mgfX lam hy0 hY1 hc0 hYc]
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- `∫₀¹ max(y, 1-y)^l dy = 2 (1 - 2^{-(l+1)})/(l+1)`. -/
lemma integral_maxfold_pow (l : ℕ) :
    ∫ y in (0 : ℝ)..1, (max y (1 - y)) ^ l = 2 * (1 - (1 / 2 : ℝ) ^ (l + 1)) / (l + 1) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => (max y (1 - y)) ^ l) volume a b :=
    fun a b => (Continuous.intervalIntegrable (by fun_prop) a b)
  have hlo : Set.EqOn (fun y : ℝ => (max y (1 - y)) ^ l) (fun y => (1 - y) ^ l) (Set.uIcc 0 (1 / 2)) := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    simp only [max_eq_right (by linarith [hy.2] : y ≤ 1 - y)]
  have hhi : Set.EqOn (fun y : ℝ => (max y (1 - y)) ^ l) (fun y => y ^ l) (Set.uIcc (1 / 2) 1) := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    simp only [max_eq_left (by linarith [hy.1] : 1 - y ≤ y)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / 2)) (hint (1 / 2) 1),
    intervalIntegral.integral_congr hlo, intervalIntegral.integral_congr hhi,
    intervalIntegral.integral_comp_sub_left (fun y => y ^ l), integral_pow, integral_pow]
  field_simp
  ring

/-- **The row-`s` factor** (`Ex` of the template) in closed form, for `l_u = l ∈ ℕ`. -/
theorem lintegral_ellUX (l : ℕ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-(l : ℝ) * ellUX N y)) ∂unif =
      ENNReal.ofReal (Real.exp ((l : ℝ) * (slT N / N)) * (2 * (1 - (1 / 2 : ℝ) ^ (l + 1)) / (l + 1))) := by
  have hpt : ∀ y ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(l : ℝ) * ellUX N y) =
      Real.exp ((l : ℝ) * (slT N / N)) * (max y (1 - y)) ^ l := by
    intro y hy
    have hcy : clamp01 y = y := by
      unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy.1]
    have hpos : 0 < max y (1 - y) := by
      rcases le_total y (1 / 2) with h | h
      · exact lt_max_of_lt_right (by linarith)
      · exact lt_max_of_lt_left (by linarith)
    unfold ellUX
    rw [hcy, ← Real.exp_log (pow_pos hpos l), ← Real.exp_add, Real.log_pow]
    congr 1; ring
  unfold unif
  rw [setLIntegral_congr_fun measurableSet_Icc (fun y hy => congrArg ENNReal.ofReal (hpt y hy)),
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul, integral_maxfold_pow]
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · refine Filter.Eventually.of_forall fun y => mul_nonneg (Real.exp_pos _).le (pow_nonneg ?_ _)
    have := le_max_left y (1 - y); have := le_max_right y (1 - y); show (0 : ℝ) ≤ max y (1 - y); linarith

lemma gX_continuousOn (lam : ℕ) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y => gX lam c y) (Set.Icc a 1) := by
  have hy : ∀ y ∈ Set.Icc a 1, y ≠ 0 := fun y hy => (lt_of_lt_of_le ha hy.1).ne'
  have hmin : ContinuousOn (fun y : ℝ => min y c) (Set.Icc a 1) :=
    ContinuousOn.inf continuousOn_id continuousOn_const
  have hcy : ContinuousOn (fun y : ℝ => min 1 (c / y)) (Set.Icc a 1) :=
    ContinuousOn.inf continuousOn_const (ContinuousOn.div continuousOn_const continuousOn_id hy)
  unfold gX
  refine ContinuousOn.add (ContinuousOn.mul ((continuousOn_const.mul hmin).sub continuousOn_id)
    (hcy.pow lam)) (ContinuousOn.div ?_ ?_ fun y hy' => ?_)
  · exact ((continuousOn_const.add continuousOn_id).pow _).sub ((continuousOn_const.mul hmin).pow _)
  · exact continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).pow _)
  · have := hy y hy'
    positivity

lemma gX_nonneg (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    0 ≤ gX lam c y := by
  rw [← integral_maxpow lam hy hy1 hc hcy]
  refine intervalIntegral.integral_nonneg zero_le_one fun u _ => pow_nonneg ?_ _
  exact le_trans (le_min zero_le_one (div_nonneg hc.le hy.le)) (le_max_right _ _)

/-- **The `J` factor of a cause cell**: the template's outer lintegral is at most
`exp(λK) · ∫_{m_lo}^1 y^p gX λ c_m y dy` (`p = t - λ_u ≥ 0`). -/
theorem cell_J_le (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1)
    (hm1 : (c.1 : ℝ) ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        ∫ y in (c.1 : ℝ)..1, y ^ (t - lamU) * gX lam (c.2 : ℝ) y) := by
  set K := 7 * deltaU N + (slV N + Real.log 2) / N
  set a : ℝ := (c.1 : ℝ)
  have hset : {y : ℝ | a ≤ clamp01 y} ∩ Set.Icc 0 1 = Set.Icc a 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : clamp01 y = y := by unfold clamp01; rw [min_eq_right h3, max_eq_right h2]
      exact ⟨this ▸ h1, h3⟩
    · rintro ⟨h1, h3⟩
      have h2 : 0 ≤ y := le_trans hm0.le h1
      have : clamp01 y = y := by unfold clamp01; rw [min_eq_right h3, max_eq_right h2]
      refine ⟨?_, h2, h3⟩
      rw [this]; exact h1
  have hW : MeasurableSet {y : ℝ | a ≤ clamp01 y} := measurableSet_le measurable_const clamp01_measurable
  unfold unif
  rw [Measure.restrict_restrict hW, hset]
  have hcont : ContinuousOn (fun y => Real.exp ((lam : ℝ) * K) * (y ^ (t - lamU) * gX lam (c.2 : ℝ) y))
      (Set.Icc a 1) :=
    continuousOn_const.mul ((ContinuousOn.rpow_const continuousOn_id fun y _ =>
      Or.inr (sub_nonneg.2 hp)).mul (gX_continuousOn lam _ hm0))
  calc ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂volume.restrict (Set.Icc 0 1)
      ≤ ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * gX lam (c.2 : ℝ) y)) := by
        refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hcy : clamp01 y = y := by
          unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy0.le]
        have hin := inner_mgf_le (N := N) lam c hcm (y := y) (by rw [hcy]; exact hy0)
        unfold unif at hin
        rw [hcy] at hin ⊢
        have hexp : Real.exp ((lamU - t) * -Real.log y) = y ^ (t - lamU) := by
          rw [Real.rpow_def_of_pos hy0]; ring_nf
        rw [hexp]
        calc ENNReal.ofReal (y ^ (t - lamU)) * ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))
              ∂volume.restrict (Set.Icc 0 1)
            ≤ ENNReal.ofReal (y ^ (t - lamU)) * ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
                gX lam (c.2 : ℝ) y) := by gcongr
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]; congr 1; ring
    _ = ENNReal.ofReal (∫ y in Set.Icc a 1, Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * gX lam (c.2 : ℝ) y)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
        refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.rpow_nonneg hy0.le _)
          (gX_nonneg lam hy0 hy.2 (by linarith) (by have := hy.2; linarith)))
    _ = _ := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm1,
          intervalIntegral.integral_const_mul]

/-- **Explicit bound for one cause cell** (integer multipliers `λ`, `l_u`; real tilt `t ≥ l_u`). -/
theorem cellEvX_prob_explicit (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ)
    (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1) (hm1 : (c.1 : ℝ) ≤ 1)
    (hr0s : r0 ≠ s) (hr1s : flipAt x r0 ≠ s) (lam lu : ℕ) {t : ℝ} (ht : (lu : ℝ) ≤ t) :
    cubeM N {w : Param N | CellEvX N s r0 x .cause c w} ≤
      ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) *
        ((Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
            ∫ y in (c.1 : ℝ)..1, y ^ (t - lu) * gX lam (c.2 : ℝ) y) *
          (Real.exp ((lu : ℝ) * (slT N / N)) * (2 * (1 - (1 / 2 : ℝ) ^ (lu + 1)) / (lu + 1)))) ^ N) := by
  have hI0 : 0 ≤ ∫ y in (c.1 : ℝ)..1, y ^ (t - lu) * gX lam (c.2 : ℝ) y := by
    refine intervalIntegral.integral_nonneg hm1 fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
    exact mul_nonneg (Real.rpow_nonneg hy0.le _)
      (gX_nonneg lam hy0 hy.2 (by linarith) (by have := hy.2; linarith))
  have hlu0 : (0 : ℝ) ≤ lu := Nat.cast_nonneg _
  refine cellEvX_prob hN s r0 x c hcm hr0s hr1s t lu lam (le_trans hlu0 ht) hlu0
    (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le hI0)
    (mul_nonneg (Real.exp_pos _).le (div_nonneg (mul_nonneg zero_le_two
      (sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num)))) (by positivity))) ?_ ?_
  · exact cell_J_le lam c hcm hm0 hm1 ht
  · rw [show -(lu : ℝ) = -((lu : ℕ) : ℝ) from rfl, lintegral_ellUX lu]

end Census
end IIT
