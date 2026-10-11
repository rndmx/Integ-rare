/-
Census, B1 forced leaf 17 (`joint_x2`, agent "forcedE"), part 3: soundness and the joint bound.

The event `RegEvX (cause) ∧ 4 |NegX| < N` is a union of 61 cell events.  On a cell, the RS template of
`B1RegRS` gets one more linear constraint, `∑_j 1[(27/25) y_{r0,j} ≤ y_{r0^x,j}] ≤ (N+3)/4`, folded into the
V-functional with multiplier `ν = e log 2` (`e ≤ 2`):
`g₂ = λ gXev + ν (1_Neg - (N+3)/(4N))`.  Per unit, `E_U e^{-g₂} ≤ e^{λK + ν(N+3)/(4N)} (gX - (1 - 2^{-e}) bX⁺)`
(pointwise: on `Neg` the V-integrand is `((y+U)/(2y))^λ` and `e^{-ν} = 1 - β`).  The certificate
`B1ForcedECertX2` gives rate `1.07 > RJ` on every cell.
-/
import IIT.Census.B1ForcedECertX2
import IIT.Census.CertRSXSound
import IIT.Census.B1ForcedB1

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology

variable {N : ℕ}

/-- The `Neg` indicator of one unit (base entry `y`, competitor entry `u`). -/
noncomputable def negInd (y u : ℝ) : ℝ := if 27 / 25 * clamp01 y ≤ clamp01 u then 1 else 0

/-- `ν = e log 2`. -/
noncomputable def nuE (e : ℕ) : ℝ := e * Real.log 2

/-- `β = 1 - 2^{-e} = 1 - e^{-ν}`. -/
noncomputable def betaE (e : ℕ) : ℝ := 1 - 1 / 2 ^ e

/-- The combined per-unit functional of the joint template. -/
noncomputable def gX2ev (N : ℕ) (c : ℚ × ℚ) (lam e : ℕ) (y u : ℝ) : ℝ :=
  (lam : ℝ) * gXev N c y u + nuE e * (negInd y u - ((N : ℝ) + 3) / 4 / N)

/-- The positive part of `bX` (equal to the `Neg` integral for every `y > 0`). -/
noncomputable def bXp (lam : ℕ) (y : ℝ) : ℝ := max (bX lam y) 0

lemma nuE_nonneg (e : ℕ) : 0 ≤ nuE e := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos one_lt_two).le

lemma betaE_nonneg (e : ℕ) : 0 ≤ betaE e := by
  unfold betaE
  have : (1 : ℝ) / 2 ^ e ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  linarith

lemma betaE_le_one (e : ℕ) : betaE e ≤ 1 := by
  unfold betaE
  have : (0 : ℝ) < 1 / 2 ^ e := by positivity
  linarith

lemma exp_neg_nuE (e : ℕ) : Real.exp (-nuE e) = 1 - betaE e := by
  unfold nuE betaE
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
  ring

lemma measurable_gXev (N : ℕ) (c : ℚ × ℚ) : Measurable fun p : ℝ × ℝ => gXev N c p.1 p.2 := by
  unfold gXev
  have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
  have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
  refine (Measurable.min ?_ ?_).sub_const _
  · exact Real.measurable_log.comp ((measurable_const.mul hy).div (hy.add hu))
  · exact (measurable_const.max (Real.measurable_log.comp (hy.div_const _))).sub_const _

lemma measurable_negInd : Measurable fun p : ℝ × ℝ => negInd p.1 p.2 := by
  unfold negInd
  exact Measurable.ite (measurableSet_le ((clamp01_measurable.comp measurable_fst).const_mul _)
    (clamp01_measurable.comp measurable_snd)) measurable_const measurable_const

lemma measurable_gX2ev (N : ℕ) (c : ℚ × ℚ) (lam e : ℕ) :
    Measurable fun p : ℝ × ℝ => gX2ev N c lam e p.1 p.2 := by
  unfold gX2ev
  exact ((measurable_gXev N c).const_mul _).add ((measurable_negInd.sub_const _).const_mul _)

/-! ### The cell event inside the joint template -/

lemma x2_sub_template (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ)
    (hcm : (1 : ℝ) / 2 ≤ c.2) (lam e : ℕ) :
    {w : Param N | CellEvX N s r0 x .cause c w ∧ 4 * (NegX w r0 x).card < N} ⊆
      {w | (∀ i, w ((fun _ : Fin N => r0) i) i ∈ {y : ℝ | (c.1 : ℝ) ≤ clamp01 y}) ∧
        ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ≤ x0 * N + slT N ∧
        ∑ i, ellUX N (w ((fun _ : Fin N => s) i) i) ≤
          ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, gX2ev N c lam e (w ((fun _ : Fin N => r0) i) i) (w ((fun _ : Fin N => flipAt x r0) i) i)
          ≤ 0} := by
  rintro w ⟨hc, hneg⟩
  obtain ⟨h1, h2, h3, h4⟩ := cellEvX_sub_template hN s r0 x c hcm hc
  refine ⟨h1, h2, h3, ?_⟩
  have h4' : ∑ i, gXev N c (w r0 i) (w (flipAt x r0) i) ≤ 0 := h4
  show ∑ i, gX2ev N c lam e (w r0 i) (w (flipAt x r0) i) ≤ 0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcnt : ∑ i, negInd (w r0 i) (w (flipAt x r0) i) ≤ ((N : ℝ) + 3) / 4 := by
    have e1 : ∑ i, negInd (w r0 i) (w (flipAt x r0) i) =
        ((univ.filter fun j => 27 / 25 * clamp01 (w r0 j) ≤ clamp01 (w (flipAt x r0) j)).card : ℝ) := by
      unfold negInd; rw [Finset.sum_boole]
    have hsub : (univ.filter fun j => 27 / 25 * clamp01 (w r0 j) ≤ clamp01 (w (flipAt x r0) j)) ⊆
        insert x (NegX w r0 x) := by
      intro j hj
      rw [mem_filter] at hj
      by_cases hjx : j = x
      · rw [hjx]; exact mem_insert_self _ _
      · refine mem_insert_of_mem ?_
        unfold NegX
        exact mem_filter.2 ⟨mem_erase.2 ⟨hjx, mem_univ _⟩, hj.2⟩
    have hc1 := (card_le_card hsub).trans (card_insert_le _ _)
    have hc1' : ((univ.filter fun j => 27 / 25 * clamp01 (w r0 j) ≤ clamp01 (w (flipAt x r0) j)).card : ℝ)
        ≤ (NegX w r0 x).card + 1 := by exact_mod_cast hc1
    have hn' : (4 : ℝ) * (NegX w r0 x).card + 1 ≤ N := by exact_mod_cast hneg
    rw [e1]; linarith
  have hsplit : ∑ i, gX2ev N c lam e (w r0 i) (w (flipAt x r0) i) =
      (lam : ℝ) * ∑ i, gXev N c (w r0 i) (w (flipAt x r0) i) +
        nuE e * (∑ i, negInd (w r0 i) (w (flipAt x r0) i) - ((N : ℝ) + 3) / 4) := by
    unfold gX2ev
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have : (N : ℝ) * (((N : ℝ) + 3) / 4 / N) = ((N : ℝ) + 3) / 4 := by field_simp
    rw [this]
  rw [hsplit]
  have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  have := mul_nonpos_of_nonneg_of_nonpos hl h4'
  have := mul_nonpos_of_nonneg_of_nonpos (nuE_nonneg e) (by linarith : ∑ i, negInd (w r0 i)
    (w (flipAt x r0) i) - ((N : ℝ) + 3) / 4 ≤ 0)
  linarith

/-! ### The per-unit factor -/

lemma bX_nonpos_of_gt (lam : ℕ) {y : ℝ} (hy : 0 < y) (hr : 1 < 27 / 25 * y) : bX lam y ≤ 0 := by
  unfold bX
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  rw [sub_nonpos]
  exact pow_le_pow_left₀ (by linarith) (by linarith) _

lemma bX_continuousOn (lam : ℕ) {a : ℝ} (ha : 0 < a) : ContinuousOn (fun y => bX lam y) (Set.Icc a 1) := by
  unfold bX
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_
  have : 0 < y := lt_of_lt_of_le ha hy.1
  positivity

lemma bXp_continuousOn (lam : ℕ) {a : ℝ} (ha : 0 < a) : ContinuousOn (fun y => bXp lam y) (Set.Icc a 1) :=
  (bX_continuousOn lam ha).sup continuousOn_const

lemma bXp_le_gX (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    bXp lam y ≤ gX lam c y := by
  unfold bXp
  refine max_le ?_ (gX_nonneg lam hy hy1 hc hcy)
  by_cases hr : 27 / 25 * y ≤ 1
  · exact bX_le_gX lam hy hy1 hc hcy hr
  · exact (bX_nonpos_of_gt lam hy (lt_of_not_ge hr)).trans (gX_nonneg lam hy hy1 hc hcy)

lemma gX_sub_nonneg (lam e : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    0 ≤ gX lam c y - betaE e * bXp lam y := by
  have h1 := bXp_le_gX lam hy hy1 hc hcy
  have h2 : 0 ≤ bXp lam y := le_max_right _ _
  have := mul_le_of_le_one_left h2 (betaE_le_one e)
  linarith

/-- **The inner factor**: `E_U e^{-g₂(y, U)} ≤ e^{λK + ν(N+3)/(4N)} (gX - β bX⁺)` for `y ∈ (0, 1]`. -/
theorem inner_x2_le (lam e : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-1 * gX2ev N c lam e y u)) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N) +
          nuE e * (((N : ℝ) + 3) / 4 / N)) * (gX lam (c.2 : ℝ) y - betaE e * bXp lam y)) := by
  set K := 7 * deltaU N + (slV N + Real.log 2) / N with hK
  set A' := nuE e * (((N : ℝ) + 3) / 4 / N) with hA'
  set Cc := Real.exp ((lam : ℝ) * K + A') with hCc
  set β := betaE e with hβ
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hyc : y ≤ 2 * (c.2 : ℝ) := by linarith
  have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy1, max_eq_right hy0.le]
  set Lw : ℝ → ℝ := fun u => ((y + u) / (2 * y)) ^ lam with hLw
  set h : ℝ → ℝ := Set.indicator (Set.Ici (27 / 25 * y)) Lw with hh
  set Mx : ℝ → ℝ := fun u => (max ((y + u) / (2 * y)) (min 1 ((c.2 : ℝ) / y))) ^ lam with hMx
  have hLwc : Continuous Lw := by simp only [hLw]; fun_prop
  have hMxc : Continuous Mx := by
    simp only [hMx]
    have : Continuous fun u : ℝ => (y + u) / (2 * y) := by fun_prop
    exact (this.max continuous_const).pow _
  have hβ0 : 0 ≤ β := betaE_nonneg e
  have hβ1 : β ≤ 1 := betaE_le_one e
  have hLw0 : ∀ u, 0 ≤ u → 0 ≤ Lw u := fun u hu => pow_nonneg (div_nonneg (by linarith) (by positivity)) _
  have hh0 : ∀ u, 0 ≤ u → 0 ≤ h u := fun u hu => by
    simp only [hh, Set.indicator]; split_ifs
    · exact hLw0 u hu
    · exact le_rfl
  have hhM : ∀ u, 0 ≤ u → h u ≤ Mx u := fun u hu => by
    simp only [hh, Set.indicator]; split_ifs
    · exact pow_le_pow_left₀ (div_nonneg (by linarith) (by positivity)) (le_max_left _ _) _
    · exact pow_nonneg (le_trans (le_min zero_le_one (div_nonneg hc0.le hy0.le)) (le_max_right _ _)) _
  have hH0 : ∀ u, 0 ≤ u → 0 ≤ Mx u - β * h u := fun u hu => by
    have := mul_le_of_le_one_left (hh0 u hu) hβ1
    linarith [hhM u hu]
  -- pointwise
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.exp (-1 * gX2ev N c lam e y u) ≤ Cc * (Mx u - β * h u) := by
    intro u hu
    have hcu : clamp01 u = u := by unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]
    -- the V part
    have hV : Real.exp (-(lam : ℝ) * gXev N c y u) ≤ Real.exp ((lam : ℝ) * K) * Mx u := by
      rw [show Mx u = Real.exp (-(lam : ℝ) * min (Real.log (2 * y / (y + u)))
          (max 0 (Real.log (y / c.2)))) from (mgfX_pointwise lam hy0 hc0 hu.1).symm, ← Real.exp_add,
        Real.exp_le_exp]
      unfold gXev
      rw [hcu, hcy]
      have hmin : min (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c.2))) - 7 * deltaU N ≤
          min (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c.2)) - 7 * deltaU N) := by
        have hδ : 0 ≤ deltaU N := by unfold deltaU; positivity
        rcases le_total (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c.2))) with h' | h'
        · rw [min_eq_left h']; exact le_min (by linarith) (by linarith)
        · rw [min_eq_right h']; exact le_min (by linarith) le_rfl
      have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
      simp only [hK]
      nlinarith [mul_le_mul_of_nonneg_left hmin hl]
    have hsplit : Real.exp (-1 * gX2ev N c lam e y u) =
        Real.exp (-(lam : ℝ) * gXev N c y u) * Real.exp (-(nuE e * negInd y u)) * Real.exp A' := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold gX2ev; rw [hA']; ring
    rw [hsplit]
    have hA0 : 0 < Real.exp A' := Real.exp_pos _
    have hCc' : Cc = Real.exp ((lam : ℝ) * K) * Real.exp A' := by rw [hCc, Real.exp_add]
    by_cases hr : 27 / 25 * y ≤ u
    · have hind : negInd y u = 1 := by unfold negInd; rw [hcy, hcu, if_pos hr]
      have hhu : h u = Lw u := by simp only [hh]; exact Set.indicator_of_mem (show u ∈ Set.Ici (27 / 25 * y) from hr) _
      have hMu : Mx u = Lw u := by
        simp only [hMx, hLw]
        congr 1
        refine max_eq_left (le_trans (min_le_left _ _) ?_)
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [hind, mul_one, exp_neg_nuE, hhu, hCc', show Mx u - β * Lw u = (1 - β) * Mx u by rw [hMu]; ring]
      have h1b : 0 ≤ 1 - β := by linarith
      calc Real.exp (-(lam : ℝ) * gXev N c y u) * (1 - β) * Real.exp A'
          ≤ Real.exp ((lam : ℝ) * K) * Mx u * (1 - β) * Real.exp A' := by gcongr
        _ = _ := by ring
    · have hind : negInd y u = 0 := by unfold negInd; rw [hcy, hcu, if_neg hr]
      have hhu : h u = 0 := by
        simp only [hh]; exact Set.indicator_of_notMem (show u ∉ Set.Ici (27 / 25 * y) from hr) _
      rw [hind, mul_zero, neg_zero, Real.exp_zero, mul_one, hhu, mul_zero, sub_zero, hCc']
      calc Real.exp (-(lam : ℝ) * gXev N c y u) * Real.exp A'
          ≤ Real.exp ((lam : ℝ) * K) * Mx u * Real.exp A' := by gcongr
        _ = _ := by ring
  -- integrability
  have hhI : ∀ a b : ℝ, a ≤ b → IntervalIntegrable h volume a b := fun a b hab => by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (hLwc.integrableOn_Icc).indicator measurableSet_Ici
  have hHI : IntegrableOn (fun u => Cc * (Mx u - β * h u)) (Set.Icc 0 1) volume := by
    refine Integrable.const_mul (Integrable.sub hMxc.integrableOn_Icc (Integrable.const_mul ?_ _)) _
    exact (hLwc.integrableOn_Icc).indicator measurableSet_Ici
  -- the `Neg` integral
  have hhint : bXp lam y ≤ ∫ u in (0 : ℝ)..1, h u := by
    by_cases hr : 27 / 25 * y ≤ 1
    · have hb : bXp lam y = bX lam y := max_eq_left (bX_nonneg lam hy0 hr)
      have h0r : (0 : ℝ) ≤ 27 / 25 * y := by positivity
      rw [hb, ← intervalIntegral.integral_add_adjacent_intervals (hhI 0 _ h0r) (hhI _ 1 hr)]
      have hA : 0 ≤ ∫ u in (0 : ℝ)..(27 / 25 * y), h u :=
        intervalIntegral.integral_nonneg h0r fun u hu => hh0 u hu.1
      have hB : ∫ u in (27 / 25 * y)..1, h u = bX lam y := by
        rw [← integral_negPart lam hy0]
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le hr] at hu
        simp only [hh]
        exact Set.indicator_of_mem (show u ∈ Set.Ici (27 / 25 * y) from hu.1) _
      linarith
    · have hb : bXp lam y = 0 := max_eq_right (bX_nonpos_of_gt lam hy0 (lt_of_not_ge hr))
      rw [hb]
      exact intervalIntegral.integral_nonneg zero_le_one fun u hu => hh0 u hu.1
  have hMint : ∫ u in (0 : ℝ)..1, Mx u = gX lam (c.2 : ℝ) y := integral_maxpow lam hy0 hy1 hc0 hyc
  calc ∫⁻ u, ENNReal.ofReal (Real.exp (-1 * gX2ev N c lam e y u)) ∂unif
      ≤ ∫⁻ u in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Cc * (Mx u - β * h u)) := by
        unfold unif
        exact setLIntegral_mono' measurableSet_Icc fun u hu => ENNReal.ofReal_le_ofReal (hpt u hu)
    _ = ENNReal.ofReal (∫ u in Set.Icc (0 : ℝ) 1, Cc * (Mx u - β * h u)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hHI]
        refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun u hu => ?_
        exact mul_nonneg (Real.exp_pos _).le (hH0 u hu.1)
    _ ≤ ENNReal.ofReal (Cc * (gX lam (c.2 : ℝ) y - β * bXp lam y)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
            (hMxc.intervalIntegrable 0 1) ((hhI 0 1 zero_le_one).const_mul β),
          intervalIntegral.integral_const_mul, hMint]
        have := mul_le_mul_of_nonneg_left hhint hβ0
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

/-- **The `J` factor of a joint-X2 cell.** -/
theorem cell_J2_le (lam e : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1)
    (hm1 : (c.1 : ℝ) ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-1 * gX2ev N c lam e y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N) +
          nuE e * (((N : ℝ) + 3) / 4 / N)) *
        ∫ y in (c.1 : ℝ)..1, y ^ (t - lamU) * (gX lam (c.2 : ℝ) y - betaE e * bXp lam y)) := by
  set Kc := (lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N) + nuE e * (((N : ℝ) + 3) / 4 / N)
  set a : ℝ := (c.1 : ℝ)
  have hc0 : (0 : ℝ) < c.2 := by linarith
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
  have hcont : ContinuousOn (fun y => Real.exp Kc *
      (y ^ (t - lamU) * (gX lam (c.2 : ℝ) y - betaE e * bXp lam y))) (Set.Icc a 1) :=
    continuousOn_const.mul ((ContinuousOn.rpow_const continuousOn_id fun y _ =>
      Or.inr (sub_nonneg.2 hp)).mul ((gX_continuousOn lam _ hm0).sub
        (continuousOn_const.mul (bXp_continuousOn lam hm0))))
  calc ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-1 * gX2ev N c lam e y u)) ∂volume.restrict (Set.Icc 0 1)
      ≤ ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp Kc *
          (y ^ (t - lamU) * (gX lam (c.2 : ℝ) y - betaE e * bXp lam y))) := by
        refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hcy : clamp01 y = y := by
          unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy0.le]
        have hin := inner_x2_le (N := N) lam e c hcm hy0 hy.2
        unfold unif at hin
        rw [hcy]
        have hexp : Real.exp ((lamU - t) * -Real.log y) = y ^ (t - lamU) := by
          rw [Real.rpow_def_of_pos hy0]; ring_nf
        rw [hexp]
        calc ENNReal.ofReal (y ^ (t - lamU)) * ∫⁻ u, ENNReal.ofReal (Real.exp (-1 * gX2ev N c lam e y u))
              ∂volume.restrict (Set.Icc 0 1)
            ≤ ENNReal.ofReal (y ^ (t - lamU)) * ENNReal.ofReal (Real.exp Kc *
                (gX lam (c.2 : ℝ) y - betaE e * bXp lam y)) := by gcongr
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]; congr 1; ring
    _ = ENNReal.ofReal (∫ y in Set.Icc a 1, Real.exp Kc *
          (y ^ (t - lamU) * (gX lam (c.2 : ℝ) y - betaE e * bXp lam y))) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
        refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.rpow_nonneg hy0.le _)
          (gX_sub_nonneg lam e hy0 hy.2 hc0 (by linarith [hy.2])))
    _ = _ := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm1,
          intervalIntegral.integral_const_mul]

/-- **One joint-X2 cell, explicit bound.** -/
theorem cellX2_prob_explicit (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ)
    (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1) (hm1 : (c.1 : ℝ) ≤ 1)
    (hr0s : r0 ≠ s) (hr1s : flipAt x r0 ≠ s) (lam lu e : ℕ) {t : ℝ} (ht : (lu : ℝ) ≤ t) :
    cubeM N {w : Param N | CellEvX N s r0 x .cause c w ∧ 4 * (NegX w r0 x).card < N} ≤
      ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) *
        ((Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N) + nuE e * (((N : ℝ) + 3) / 4 / N)) *
            ∫ y in (c.1 : ℝ)..1, y ^ (t - lu) * (gX lam (c.2 : ℝ) y - betaE e * bXp lam y)) *
          (Real.exp ((lu : ℝ) * (slT N / N)) * (2 * (1 - (1 / 2 : ℝ) ^ (lu + 1)) / (lu + 1)))) ^ N) := by
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hI0 : 0 ≤ ∫ y in (c.1 : ℝ)..1, y ^ (t - lu) * (gX lam (c.2 : ℝ) y - betaE e * bXp lam y) := by
    refine intervalIntegral.integral_nonneg hm1 fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
    exact mul_nonneg (Real.rpow_nonneg hy0.le _) (gX_sub_nonneg lam e hy0 hy.2 hc0 (by linarith [hy.2]))
  have hlu0 : (0 : ℝ) ≤ lu := Nat.cast_nonneg _
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellU : Measurable (ellUX N) := by
    unfold ellUX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  have hW : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ clamp01 y} :=
    measurableSet_le measurable_const clamp01_measurable
  refine (measure_mono (x2_sub_template hN s r0 x c hcm lam e)).trans ?_
  refine joint_template_real (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => hr0s) (fun _ => hr1s)
    (fun y => -Real.log (clamp01 y)) (ellUX N) (gX2ev N c lam e) hell hellU (measurable_gX2ev N c lam e)
    _ hW (x0 * N + slT N) t lu 1 (le_trans hlu0 ht) hlu0 zero_le_one
    (mul_nonneg (Real.exp_pos _).le hI0)
    (mul_nonneg (Real.exp_pos _).le (div_nonneg (mul_nonneg zero_le_two
      (sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num)))) (by positivity))) ?_ ?_
  · exact cell_J2_le lam e c hcm hm0 hm1 ht
  · rw [show -(lu : ℝ) = -((lu : ℕ) : ℝ) from rfl, lintegral_ellUX lu]

/-! ### The certified cells -/

/-- **Soundness of one certified cell**: `I₂ ≤ ub` and the rate inequality. -/
theorem x2Cell_sound (C : X2Cell) (h : x2CellOK C = true) :
    0 < C.v ∧ C.v ≤ C.w ∧ C.w ≤ 1 ∧ C.v < 1 ∧ (1 : ℚ) / 2 ≤ C.w ^ 4 ∧ C.e ≤ 2 ∧
    (∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * (gX C.lam ((C.w : ℝ) ^ 4) y - betaE C.e * bXp C.lam y))
      ≤ C.ub ∧
    Real.log 2 + Real.log (Real.exp (nuE C.e / 4) * C.ub) + Real.log (rsEx C.lu : ℝ) +
      ((C.P : ℝ) / 4 + C.lu) * x0 ≤ -(x2R : ℝ) ∧ (0 : ℝ) < C.ub := by
  simp only [x2CellOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, hk⟩, hp⟩, h0⟩, h1⟩, he2⟩, hevq⟩, hub⟩, hq⟩, hx⟩, hhi⟩,
    hrate⟩ := h
  have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
  have hw' : (0 : ℝ) < C.w := by exact_mod_cast (lt_of_lt_of_le hv hvw)
  have hvw' : (C.v : ℝ) ^ 4 ≤ (C.w : ℝ) ^ 4 := pow_le_pow_left₀ hv'.le (by exact_mod_cast hvw) 4
  have hw1' : (C.w : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hw'.le (by exact_mod_cast hw1)
  have hv1' : (C.v : ℝ) ^ 4 ≤ 1 := hvw'.trans hw1'
  have hc0 : (0 : ℝ) < (C.w : ℝ) ^ 4 := by positivity
  have hw2' : (1 : ℝ) / 2 ≤ (C.w : ℝ) ^ 4 := by
    have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this; exact this
  have hp0 : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
  set p : ℝ := (C.P : ℝ) / 4
  set a : ℝ := (C.v : ℝ) ^ 4
  set G : ℝ → ℝ := fun y => y ^ p * gX C.lam ((C.w : ℝ) ^ 4) y
  set Bp : ℝ → ℝ := fun y => y ^ p * bXp C.lam y
  have ha0 : 0 < a := by positivity
  have hGc : ContinuousOn G (Set.Icc a 1) :=
    (ContinuousOn.rpow_const continuousOn_id fun y _ => Or.inr hp0).mul (gX_continuousOn C.lam _ ha0)
  have hBc : ContinuousOn Bp (Set.Icc a 1) :=
    (ContinuousOn.rpow_const continuousOn_id fun y _ => Or.inr hp0).mul (bXp_continuousOn C.lam ha0)
  have hGI : IntervalIntegrable G volume a 1 := by
    refine ContinuousOn.intervalIntegrable ?_; rw [Set.uIcc_of_le hv1']; exact hGc
  have hBI : IntervalIntegrable Bp volume a 1 := by
    refine ContinuousOn.intervalIntegrable ?_; rw [Set.uIcc_of_le hv1']; exact hBc
  have hsplit : (∫ y in a..1, y ^ p * (gX C.lam ((C.w : ℝ) ^ 4) y - betaE C.e * bXp C.lam y)) =
      (∫ y in a..1, G y) - betaE C.e * ∫ y in a..1, Bp y := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hGI (hBI.const_mul _)]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [G, Bp]; ring
  have hGeq : (∫ y in a..1, G y) = ((cellIq C.v C.w C.lam C.P : ℚ) : ℝ) :=
    (cellIq_eq C.v C.w hv hvw hw1 C.lam C.P (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp h0 h1).symm
  have hBlow : ((1 : ℝ) - 1 / 2 ^ C.e) * ((bIq C.v x2q C.lam C.P : ℚ) : ℝ) ≤
      betaE C.e * ∫ y in a..1, Bp y := by
    rcases hevq with he0 | hvq
    · have : ((1 : ℝ) - 1 / 2 ^ C.e) = 0 := by rw [he0]; norm_num
      rw [this, zero_mul]
      refine mul_nonneg (betaE_nonneg _) (intervalIntegral.integral_nonneg hv1' fun y hy => ?_)
      exact mul_nonneg (Real.rpow_nonneg (le_trans ha0.le hy.1) _) (le_max_right _ _)
    · unfold betaE
      refine mul_le_mul_of_nonneg_left ?_ (by
        have : (1 : ℝ) / 2 ^ C.e ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
        linarith)
      have hq0 : (0 : ℝ) < (x2q : ℝ) := by unfold x2q; norm_num
      have hq4 : ((x2q : ℚ) : ℝ) ^ 4 ≤ 1 := by unfold x2q; norm_num
      have haq : a ≤ ((x2q : ℚ) : ℝ) ^ 4 := pow_le_pow_left₀ hv'.le (by exact_mod_cast hvq) 4
      rw [bIq_eq C.v x2q hv hvq C.lam C.P (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp]
      have hBI1 : IntervalIntegrable Bp volume a (((x2q : ℚ) : ℝ) ^ 4) :=
        hBI.mono_set (by rw [Set.uIcc_of_le haq, Set.uIcc_of_le hv1']; exact Set.Icc_subset_Icc le_rfl hq4)
      have hBI2 : IntervalIntegrable Bp volume (((x2q : ℚ) : ℝ) ^ 4) 1 :=
        hBI.mono_set (by rw [Set.uIcc_of_le hq4, Set.uIcc_of_le hv1']; exact Set.Icc_subset_Icc haq le_rfl)
      rw [← intervalIntegral.integral_add_adjacent_intervals hBI1 hBI2]
      have hpos : 0 ≤ ∫ y in (((x2q : ℚ) : ℝ) ^ 4)..1, Bp y :=
        intervalIntegral.integral_nonneg hq4 fun y hy => mul_nonneg
          (Real.rpow_nonneg (le_trans (by positivity) hy.1) _) (le_max_right _ _)
      have hmono : ∫ y in a..(((x2q : ℚ) : ℝ) ^ 4), y ^ ((C.P : ℝ) / 4) * bX C.lam y ≤
          ∫ y in a..(((x2q : ℚ) : ℝ) ^ 4), Bp y := by
        refine intervalIntegral.integral_mono_on haq ?_ hBI1 fun y hy => ?_
        · refine ContinuousOn.intervalIntegrable ?_
          rw [Set.uIcc_of_le haq]
          exact ((ContinuousOn.rpow_const continuousOn_id fun y _ => Or.inr hp0).mul
            (bX_continuousOn C.lam ha0)).mono (Set.Icc_subset_Icc le_rfl hq4)
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg (le_trans ha0.le hy.1) _)
      linarith
  have hubR : ((x2Iq C : ℚ) : ℝ) ≤ C.ub := by exact_mod_cast hub
  have hIq : ((x2Iq C : ℚ) : ℝ) = ((cellIq C.v C.w C.lam C.P : ℚ) : ℝ) -
      ((1 : ℝ) - 1 / 2 ^ C.e) * ((bIq C.v x2q C.lam C.P : ℚ) : ℝ) := by
    unfold x2Iq; push_cast; ring
  have hI2 : (∫ y in a..1, y ^ p * (gX C.lam ((C.w : ℝ) ^ 4) y - betaE C.e * bXp C.lam y)) ≤ C.ub := by
    rw [hsplit, hGeq]; linarith
  -- the rate
  have hEx0 : (0 : ℝ) < rsEx C.lu := by
    have : (0 : ℚ) < rsEx C.lu := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  have hub0 : (0 : ℝ) < C.ub := by
    have : (0 : ℚ) < C.ub := by
      have h2 : (0 : ℚ) < rsEx C.lu := by exact_mod_cast hEx0
      by_contra hc; push Not at hc
      have : 2 * C.ub * rsEx C.lu ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
      linarith
    exact_mod_cast this
  have hcr := crLog_le (q := 2 * C.ub * rsEx C.lu) (r := C.r) C.k C.n (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, hhi⟩)
  have hsplitL : Real.log (((2 * C.ub * rsEx C.lu : ℚ)) : ℝ) =
      Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsEx C.lu : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) hEx0.ne', Real.log_mul (by norm_num) hub0.ne']
  have ht : (0 : ℝ) ≤ (C.P : ℝ) / 4 + C.lu := by positivity
  have hx0 := cr_x0_bounds.2
  have hl2 := cr_log2_bounds.2
  have hr : ((C.r : ℚ) : ℝ) + ((C.P : ℝ) / 4 + C.lu) * (crX0hi : ℝ) + (C.e : ℝ) * (crL2hi : ℝ) / 4 ≤
      -(x2R : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this; exact this
  have hlogJ : Real.log (Real.exp (nuE C.e / 4) * C.ub) = nuE C.e / 4 + Real.log C.ub := by
    rw [Real.log_mul (Real.exp_pos _).ne' hub0.ne', Real.log_exp]
  have he0 : (0 : ℝ) ≤ C.e := Nat.cast_nonneg _
  refine ⟨hv, hvw, hw1, hv1, hw2, he2, hI2, ?_, hub0⟩
  rw [hlogJ]
  rw [hsplitL] at hcr
  unfold nuE
  have hA := mul_le_mul_of_nonneg_left hx0 ht
  have hB := mul_le_mul_of_nonneg_left hl2.le he0
  have hp' : p = (C.P : ℝ) / 4 := rfl
  rw [hp']
  linarith

/-- **One original cause cell, joint-X2 exponential bound.** -/
theorem x2Cell_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXCauseData) (hr0s : r0 ≠ s) (hr1s : flipAt x r0 ≠ s) :
    cubeM N {w : Param N | CellEvX N s r0 x .cause c w ∧ 4 * (NegX w r0 x).card < N} ≤
      ENNReal.ofReal (Real.exp (-((x2R : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N) + 2) / 2 ^ N) := by
  have hall := x2Link_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  have hok : x2CellOK C = true := (List.all_eq_true.1 x2Cells_ok) C hC
  have hb := (List.all_eq_true.1 x2Bounds) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hlu⟩, hP⟩ := hb
  simp only [x2Link, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  obtain ⟨hv, hvw, hw1, hv1, hw2, he2, hI2, hsound, hub0⟩ := x2Cell_sound C hok
  set c' : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc'
  -- monotonicity: c's event inside c''s
  have hmono := cellEvX_mono hN s r0 x (c := c) (c' := c') (by simp only [hc']; exact_mod_cast hv4)
    (by
      rcases hcap with h | h
      · left; simp only [hc']; exact_mod_cast h
      · right; simp only [hc', h]; norm_num)
    (by exact_mod_cast hc2) (by
      simp only [hc']; push_cast
      have : (0 : ℝ) < C.w := by exact_mod_cast (lt_of_lt_of_le hv hvw)
      positivity)
  have hmono' : {w : Param N | CellEvX N s r0 x .cause c w ∧ 4 * (NegX w r0 x).card < N} ⊆
      {w : Param N | CellEvX N s r0 x .cause c' w ∧ 4 * (NegX w r0 x).card < N} :=
    fun w hw => ⟨hmono hw.1, hw.2⟩
  refine (measure_mono hmono').trans ?_
  have ht : (C.lu : ℝ) ≤ (C.P : ℝ) / 4 + C.lu := by
    have : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
    linarith
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by
    simp only [hc']; have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  have hm0' : (0 : ℝ) < (c'.1 : ℝ) := by
    simp only [hc']; push_cast
    have : (0 : ℝ) < C.v := by exact_mod_cast hv
    positivity
  have hm1' : (c'.1 : ℝ) ≤ 1 := by
    simp only [hc']; push_cast
    exact pow_le_one₀ (by exact_mod_cast hv.le) (by exact_mod_cast hv1.le)
  refine (cellX2_prob_explicit hN s r0 x c' hcm' hm0' hm1' hr0s hr1s C.lam C.lu C.e ht).trans ?_
  set I := ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) *
    (gX C.lam ((C.w : ℝ) ^ 4) y - betaE C.e * bXp C.lam y) with hIdef
  have hI' : (∫ y in (c'.1 : ℝ)..1, y ^ ((C.P : ℝ) / 4 + C.lu - C.lu) *
      (gX C.lam (c'.2 : ℝ) y - betaE C.e * bXp C.lam y)) = I := by
    simp only [hc', add_sub_cancel_right]; push_cast; rfl
  rw [hI']
  have hI0 : 0 ≤ I := by
    have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
    have hw' : (0 : ℝ) < C.w := by exact_mod_cast (lt_of_lt_of_le hv hvw)
    have hv1' : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv'.le (by exact_mod_cast hv1.le)
    have hw2' : (1 : ℝ) / 2 ≤ (C.w : ℝ) ^ 4 := by
      have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this; exact this
    refine intervalIntegral.integral_nonneg hv1' fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
    exact mul_nonneg (Real.rpow_nonneg hy0.le _) (gX_sub_nonneg C.lam C.e hy0 hy.2 (by positivity)
      (by linarith [hy.2]))
  have hEx : (2 * (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1)) = (rsEx C.lu : ℝ) := by
    unfold rsEx; push_cast; ring
  rw [hEx]
  have hEx0 : (0 : ℝ) < rsEx C.lu := by
    have : (0 : ℚ) < rsEx C.lu := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  have hJ0 : 0 < Real.exp (nuE C.e / 4) * C.ub := mul_pos (Real.exp_pos _) hub0
  have hrate := rate_of_log_le hJ0 hEx0 hsound N
  set t : ℝ := (C.P : ℝ) / 4 + C.lu with htdef
  set K : ℝ := 7 * deltaU N + (slV N + Real.log 2) / N with hK
  set ν : ℝ := nuE C.e with hν
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  -- replace `I` by `ub`
  have hstep : Real.exp (t * (x0 * N + slT N)) *
      ((Real.exp ((C.lam : ℝ) * K + ν * (((N : ℝ) + 3) / 4 / N)) * I) *
        (Real.exp ((C.lu : ℝ) * (slT N / N)) * (rsEx C.lu : ℝ))) ^ N ≤
      Real.exp (t * (x0 * N + slT N)) *
      ((Real.exp ((C.lam : ℝ) * K + ν * (((N : ℝ) + 3) / 4 / N)) * C.ub) *
        (Real.exp ((C.lu : ℝ) * (slT N / N)) * (rsEx C.lu : ℝ))) ^ N := by
    gcongr
  refine (ENNReal.ofReal_le_ofReal hstep).trans ?_
  -- split the bound
  have hsplitB : Real.exp (t * (x0 * N + slT N)) *
      ((Real.exp ((C.lam : ℝ) * K + ν * (((N : ℝ) + 3) / 4 / N)) * C.ub) *
        (Real.exp ((C.lu : ℝ) * (slT N / N)) * (rsEx C.lu : ℝ))) ^ N =
      ((2 : ℝ) ^ N * (Real.exp (t * (x0 * N)) * ((Real.exp (ν / 4) * C.ub) * (rsEx C.lu : ℝ)) ^ N)) *
        Real.exp (t * slT N + (C.lam : ℝ) * (K * N) + 3 * ν / 4 + (C.lu : ℝ) * slT N) / 2 ^ N := by
    have e1 : (Real.exp ((C.lam : ℝ) * K + ν * (((N : ℝ) + 3) / 4 / N))) ^ N =
        Real.exp ((C.lam : ℝ) * (K * N) + 3 * ν / 4) * (Real.exp (ν / 4)) ^ N := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; field_simp; ring
    have e2 : (Real.exp ((C.lu : ℝ) * (slT N / N))) ^ N = Real.exp ((C.lu : ℝ) * slT N) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [mul_pow, mul_pow, mul_pow, e1, e2, mul_pow, mul_add t, Real.exp_add]
    rw [show t * slT N + (C.lam : ℝ) * (K * N) + 3 * ν / 4 + (C.lu : ℝ) * slT N =
      t * slT N + ((C.lam : ℝ) * (K * N) + 3 * ν / 4) + (C.lu : ℝ) * slT N by ring,
      Real.exp_add, Real.exp_add]
    field_simp
    rw [mul_pow, show (t * slT N * 4 + ((N : ℝ) * (C.lam : ℝ) * K * 4 + 3 * ν)) / 4 =
      t * slT N + (N : ℝ) * (C.lam : ℝ) * K + 3 * ν / 4 by ring, Real.exp_add, Real.exp_add]
    ring
  rw [hsplitB]
  -- the lower-order exponent
  have hslT : 0 ≤ slT N := by
    unfold slT
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hslV : 0 ≤ slV N := by unfold slV; positivity
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hKN : K * N ≤ 7 + slV N + 1 := by
    simp only [hK, add_mul, div_mul_cancel₀ _ hNr.ne']
    have := Real.log_two_lt_d9
    nlinarith
  have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
  have hluR : (C.lu : ℝ) ≤ 3 := by exact_mod_cast hlu
  have htR : t ≤ 11 := by
    have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
    simp only [htdef]; linarith
  have hKN0 : 0 ≤ K * N := by
    simp only [hK]; unfold deltaU; have := Real.log_pos one_lt_two; positivity
  have hν : 3 * ν / 4 ≤ 2 := by
    simp only [hν]; unfold nuE
    have : (C.e : ℝ) ≤ 2 := by exact_mod_cast he2
    have := Real.log_two_lt_d9
    have : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
    nlinarith
  have hE : t * slT N + (C.lam : ℝ) * (K * N) + 3 * ν / 4 + (C.lu : ℝ) * slT N ≤
      14 * slT N + 17 * (8 + slV N) + 2 := by
    have ht0 : 0 ≤ t := by simp only [htdef]; positivity
    have hl0 : (0 : ℝ) ≤ C.lam := Nat.cast_nonneg _
    have hu0 : (0 : ℝ) ≤ C.lu := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right htR hslT, mul_le_mul_of_nonneg_right hluR hslT,
      mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff_of_pos_right h2N]
  exact mul_le_mul hrate (Real.exp_le_exp.2 hE) (Real.exp_pos _).le (Real.exp_pos _).le

/-! ### The joint bound -/

/-- **Joint bound X2** (per far `(r0, x, σ)`, certified rate `1.07 > RJ`), with `P0X2` unfolded. -/
theorem joint_x2E : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), N ≤ 3 * ham r0 s →
    cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ (σ = .cause → N ≤ 4 * (NegX w r0 x).card)} ≤
      ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N) := by
  have hab := poly_absorb 61 0 (δ := (x2R : ℝ) - RJ) (by unfold RJ x2R; norm_num)
  filter_upwards [hab, eventually_ge_atTop 7] with N hab hN7 s r0 x σ hfar
  have hN : 0 < N := by omega
  cases σ with
  | effect =>
    have : {w : Param N | RegEvX N s r0 x .effect w ∧
        ¬ ((XSide.effect : XSide) = .cause → N ≤ 4 * (NegX w r0 x).card)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw => hw.2 fun h => by cases h
    rw [this, measure_empty]; exact bot_le
  | cause =>
    have hne : ∀ a b : State N, 3 ≤ ham a b → a ≠ b := fun a b h hab => by
      subst hab; rw [ham_self] at h; omega
    have hfar3 : 3 ≤ ham r0 s := by omega
    have hr0s : r0 ≠ s := hne _ _ hfar3
    have hr1s : flipAt x r0 ≠ s := by
      intro h
      have t1 := ham_triangle (flipAt x r0) r0 s
      have hh0 := ham_flipAt_le_one x r0
      rw [← h] at hfar3
      have : ham r0 (flipAt x r0) ≤ 1 := by rw [ham_comm]; exact hh0
      omega
    set B := Real.exp (-((x2R : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N) + 2) / 2 ^ N with hB
    have hB0 : 0 ≤ B := by positivity
    have hset : {w : Param N | RegEvX N s r0 x .cause w ∧
        ¬ ((XSide.cause : XSide) = .cause → N ≤ 4 * (NegX w r0 x).card)} ⊆
        ⋃ c ∈ cellsXCauseData.toFinset,
          {w : Param N | CellEvX N s r0 x .cause c w ∧ 4 * (NegX w r0 x).card < N} := by
      rintro w ⟨⟨c, hc, hcell⟩, hP⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      refine ⟨c, ?_, hcell, ?_⟩
      · simpa [cellsX] using hc
      · by_contra hle; exact hP fun _ => by omega
    refine (measure_mono hset).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ c ∈ cellsXCauseData.toFinset,
          cubeM N {w : Param N | CellEvX N s r0 x .cause c w ∧ 4 * (NegX w r0 x).card < N}
        ≤ ∑ _c ∈ cellsXCauseData.toFinset, ENNReal.ofReal B :=
          sum_le_sum fun c hc => x2Cell_prob hN s r0 x (List.mem_toFinset.1 hc) hr0s hr1s
      _ = (cellsXCauseData.toFinset.card : ENNReal) * ENNReal.ofReal B := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (61 : ENNReal) * ENNReal.ofReal B := by
          gcongr
          have : cellsXCauseData.toFinset.card ≤ cellsXCauseData.length := List.toFinset_card_le _
          have hlen : cellsXCauseData.length = 61 := by decide
          exact_mod_cast hlen ▸ this
      _ = ENNReal.ofReal (61 * B) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N) := by
          apply ENNReal.ofReal_le_ofReal
          have hsl := rs_slack_le N
          have hslT : 0 ≤ slT N := by
            unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
            linarith
          have hS : Real.exp (14 * slT N + 17 * (8 + slV N) + 2) ≤ Real.exp (4000 + 1400 * Real.log N) :=
            Real.exp_le_exp.2 (by linarith)
          have h2N : (0 : ℝ) < 2 ^ N := by positivity
          rw [hB, show 61 * (Real.exp (-((x2R : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N) + 2) / 2 ^ N)
              = 61 * Real.exp (14 * slT N + 17 * (8 + slV N) + 2) * Real.exp (-((x2R : ℝ) * N)) / 2 ^ N by ring,
            div_le_div_iff_of_pos_right h2N]
          have hk : 61 * Real.exp (14 * slT N + 17 * (8 + slV N) + 2) ≤ Real.exp (((x2R : ℝ) - RJ) * N) := by
            refine le_trans ?_ hab
            rw [pow_zero, mul_one]; gcongr
          have e2 : Real.exp (-(RJ * N)) = Real.exp (((x2R : ℝ) - RJ) * N) * Real.exp (-((x2R : ℝ) * N)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [e2]
          exact mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le

end Census
end IIT
