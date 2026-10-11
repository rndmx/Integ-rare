/-
Census, B1 new leaf `pairLow`: the restricted per-unit factor of the regime-X cause template.

* `pl_inner_le`: with `u` restricted to `y + u > 1 - 1/N`, the inner MGF is at most
  `e^{λK} (gX λ c y - (1-y) min(1,c/y)^λ + 1/N)` (the integrand `max((y+u)/(2y), m)^λ` is `≥ m^λ`).
* `pl_J_le`: the outer factor (copy of `cell_J_le`).
* `plCorr_eq`: the removed mass `∫_{v⁴}^1 y^{P/4} (1-y) min(1, w⁴/y)^λ dy = plCorrQ v w λ P`.
-/
import IIT.Census.B1RegRS
import IIT.Census.B1NewLeafPairCert

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-- The integrand of the max form is at least `m^λ`. -/
lemma pl_maxpow_ge (lam : ℕ) {m a : ℝ} (hm : 0 ≤ m) : m ^ lam ≤ (max a m) ^ lam :=
  pow_le_pow_left₀ hm (le_max_right _ _) lam

/-- `gX λ c y ≥ min(1, c/y)^λ`. -/
lemma pl_gX_ge (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    (min 1 (c / y)) ^ lam ≤ gX lam c y := by
  have hm : 0 ≤ min 1 (c / y) := le_min zero_le_one (div_nonneg hc.le hy.le)
  rw [← integral_maxpow lam hy hy1 hc hcy]
  have h1 : ∫ _u in (0 : ℝ)..1, (min 1 (c / y)) ^ lam = (min 1 (c / y)) ^ lam := by simp
  rw [← h1]
  exact intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun u _ => pl_maxpow_ge lam hm

/-- **The restricted inner MGF.** -/
theorem pl_inner_le (hN : 0 < N) (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {y : ℝ}
    (hy0 : 0 < clamp01 y) :
    ∫⁻ u, {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u}.indicator
        (fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))) u ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        (gX lam (c.2 : ℝ) (clamp01 y) - (1 - clamp01 y) * (min 1 ((c.2 : ℝ) / clamp01 y)) ^ lam +
          1 / N)) := by
  set Y := clamp01 y with hYdef
  have hY1 : Y ≤ 1 := clamp01_le_one y
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hYc : Y ≤ 2 * (c.2 : ℝ) := by linarith
  set K := 7 * deltaU N + (slV N + Real.log 2) / N with hK
  set m := min 1 ((c.2 : ℝ) / Y) with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (div_nonneg hc0.le hy0.le)
  have hm1 : m ≤ 1 := min_le_left _ _
  set h : ℝ → ℝ := fun u => (max ((Y + u) / (2 * Y)) m) ^ lam with hh
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- pointwise on [0,1]
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(lam : ℝ) * gXev N c y u) ≤ Real.exp ((lam : ℝ) * K) * h u := by
    intro u hu
    have hcu : clamp01 u = u := by
      unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]
    have hmgf := mgfX_pointwise lam hy0 hc0 hu.1
    rw [show h u = (max ((Y + u) / (2 * Y)) (min 1 ((c.2 : ℝ) / Y))) ^ lam from rfl, ← hmgf,
      ← Real.exp_add, Real.exp_le_exp]
    unfold gXev
    rw [hcu]
    have hmin : min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2))) - 7 * deltaU N ≤
        min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2)) - 7 * deltaU N) := by
      have hδ : 0 ≤ deltaU N := by unfold deltaU; positivity
      rcases le_total (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2))) with h' | h'
      · rw [min_eq_left h']; exact le_min (by linarith) (by linarith)
      · rw [min_eq_right h']; exact le_min (by linarith) le_rfl
    have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
    simp only [hK]
    nlinarith [mul_le_mul_of_nonneg_left hmin hl]
  set L' : ℝ := max 0 (1 - 1 / (N : ℝ) - Y) with hL'
  have hL0 : 0 ≤ L' := le_max_left _ _
  have hL1 : L' ≤ 1 := max_le zero_le_one (by
    have : 0 ≤ Y := clamp01_nonneg y
    have : 0 < 1 / (N : ℝ) := by positivity
    linarith)
  have hS : MeasurableSet {u : ℝ | 1 - 1 / (N : ℝ) < Y + clamp01 u} :=
    measurableSet_lt measurable_const (measurable_const.add clamp01_measurable)
  have hcont : Continuous h := by
    simp only [hh]
    have : (2 * Y) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  -- the restricted set
  have hsub : Set.Icc (0 : ℝ) 1 ∩ {u : ℝ | 1 - 1 / (N : ℝ) < Y + clamp01 u} ⊆ Set.Icc L' 1 := by
    rintro u ⟨hu, hu2⟩
    have hcu : clamp01 u = u := by
      unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]
    simp only [Set.mem_ofPred_eq, hcu] at hu2
    exact ⟨max_le hu.1 (by linarith), hu.2⟩
  have hint1 : ∫⁻ u, {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u}.indicator
      (fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))) u ∂unif ≤
      ∫⁻ u in Set.Icc L' 1, ENNReal.ofReal (Real.exp ((lam : ℝ) * K) * h u) := by
    rw [lintegral_indicator hS]
    unfold unif
    rw [Measure.restrict_restrict hS, Set.inter_comm]
    refine (lintegral_mono_set hsub).trans ?_
    refine setLIntegral_mono' measurableSet_Icc fun u hu => ENNReal.ofReal_le_ofReal ?_
    exact hpt u ⟨hL0.trans hu.1, hu.2⟩
  refine hint1.trans ?_
  have hpos : ∀ u, 0 ≤ Real.exp ((lam : ℝ) * K) * h u := fun u =>
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (le_max_of_le_right hm0) _)
  have hc2 : Continuous fun u => Real.exp ((lam : ℝ) * K) * h u := continuous_const.mul hcont
  rw [← ofReal_integral_eq_lintegral_ofReal hc2.integrableOn_Icc
    (Filter.Eventually.of_forall hpos), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL1, intervalIntegral.integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- ∫_{L'}^1 h = gX - ∫_0^{L'} h ≤ gX - L' m^λ
  have hint : ∀ a b : ℝ, IntervalIntegrable h volume a b := fun a b => hcont.intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 L') (hint L' 1)
  have hfull : ∫ u in (0 : ℝ)..1, h u = gX lam (c.2 : ℝ) Y := integral_maxpow lam hy0 hY1 hc0 hYc
  have hlow : L' * m ^ lam ≤ ∫ u in (0 : ℝ)..L', h u := by
    have : ∫ _u in (0 : ℝ)..L', m ^ lam = L' * m ^ lam := by simp
    rw [← this]
    exact intervalIntegral.integral_mono_on hL0 intervalIntegrable_const (hint _ _)
      fun u _ => pl_maxpow_ge lam hm0
  have hmpow : m ^ lam ≤ 1 := pow_le_one₀ hm0 hm1
  have hmpow0 : 0 ≤ m ^ lam := pow_nonneg hm0 _
  have hLge : 1 - 1 / (N : ℝ) - Y ≤ L' := le_max_right _ _
  have hNinv : 0 < 1 / (N : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hLge hmpow0, mul_le_mul_of_nonneg_left hmpow hNinv.le]

/-- The restricted per-unit integrand. -/
noncomputable def plG (N lam : ℕ) (c y : ℝ) : ℝ := gX lam c y - (1 - y) * (min 1 (c / y)) ^ lam + 1 / N

lemma plG_nonneg (N lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    0 ≤ plG N lam c y := by
  unfold plG
  have h1 := pl_gX_ge lam hy hy1 hc hcy
  have hm0 : 0 ≤ (min 1 (c / y)) ^ lam := pow_nonneg (le_min zero_le_one (div_nonneg hc.le hy.le)) _
  have : (1 - y) * (min 1 (c / y)) ^ lam ≤ (min 1 (c / y)) ^ lam := by nlinarith
  have : (0 : ℝ) ≤ 1 / N := by positivity
  linarith

lemma plG_continuousOn (N lam : ℕ) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y => plG N lam c y) (Set.Icc a 1) := by
  have hy : ∀ y ∈ Set.Icc a 1, y ≠ 0 := fun y hy => (lt_of_lt_of_le ha hy.1).ne'
  unfold plG
  refine ((gX_continuousOn lam c ha).sub ((continuousOn_const.sub continuousOn_id).mul
    ((ContinuousOn.inf continuousOn_const (ContinuousOn.div continuousOn_const continuousOn_id hy)).pow lam))).add
    continuousOn_const

/-- **The restricted `J` factor of a cause cell.** -/
theorem pl_J_le (hN : 0 < N) (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1)
    (hm1 : (c.1 : ℝ) ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u}.indicator
            (fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))) u ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        ∫ y in (c.1 : ℝ)..1, y ^ (t - lamU) * plG N lam (c.2 : ℝ) y) := by
  set K := 7 * deltaU N + (slV N + Real.log 2) / N
  set a : ℝ := (c.1 : ℝ)
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hset : {y : ℝ | a ≤ clamp01 y} ∩ Set.Icc 0 1 = Set.Icc a 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc]
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
  have hcont : ContinuousOn (fun y => Real.exp ((lam : ℝ) * K) * (y ^ (t - lamU) * plG N lam (c.2 : ℝ) y))
      (Set.Icc a 1) :=
    continuousOn_const.mul ((ContinuousOn.rpow_const continuousOn_id fun y _ =>
      Or.inr (sub_nonneg.2 hp)).mul (plG_continuousOn N lam _ hm0))
  calc ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u}.indicator
            (fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))) u ∂volume.restrict (Set.Icc 0 1)
      ≤ ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * plG N lam (c.2 : ℝ) y)) := by
        refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hcy : clamp01 y = y := by
          unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy0.le]
        have hin := pl_inner_le hN lam c hcm (y := y) (by rw [hcy]; exact hy0)
        unfold unif at hin
        rw [hcy] at hin ⊢
        have hexp : Real.exp ((lamU - t) * -Real.log y) = y ^ (t - lamU) := by
          rw [Real.rpow_def_of_pos hy0]; ring_nf
        rw [hexp]
        calc ENNReal.ofReal (y ^ (t - lamU)) * ∫⁻ u, {u : ℝ | 1 - 1 / (N : ℝ) < y + clamp01 u}.indicator
              (fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))) u ∂volume.restrict (Set.Icc 0 1)
            ≤ ENNReal.ofReal (y ^ (t - lamU)) * ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
                plG N lam (c.2 : ℝ) y) := by
              gcongr
              exact hin
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]; congr 1; ring
    _ = ENNReal.ofReal (∫ y in Set.Icc a 1, Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * plG N lam (c.2 : ℝ) y)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
        refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.rpow_nonneg hy0.le _)
          (plG_nonneg N lam hy0 hy.2 hc0 (by have := hy.2; linarith)))
    _ = _ := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm1,
          intervalIntegral.integral_const_mul]

end Census
end IIT
