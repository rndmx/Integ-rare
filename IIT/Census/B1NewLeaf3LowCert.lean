/-
Census, B1 GoodX3 leaf `lowFew`, cause side: the certificate for the only cause cell that meets the low window.

Every cause cell except `lcc0 = (0.499999, 0.5001051)` has `m_lo ≥ 0.5001 > 1/2 + e^{-N/200}`, so its rows `r0` have no
low unit.  For `lcc0` (certified partner `lcC0`, `v⁴ = 0.4999966`): the Chernoff weight `e^{6·1[y < b]}` on the
base entries costs `(e⁶ - 1) ∫_{v⁴}^{z⁴} y^{P/4} gX ≤ 403 · lowQ` per unit (`z⁴ = 1/2 + 2.0·10⁻⁷ ≥ b`), and gains
`e^{-6N/1000}`: certified unit rate `1.006` + `0.006` = `1.012 > RJ`.
-/
import IIT.Census.B1NewLeaf3Pair

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- `∫_{v⁴}^{z⁴} y^{P/4} gX λ c y dy` below the cap, as a rational. -/
def lowQ (v z : ℚ) (lam P : ℕ) : ℚ :=
  (1 - 2 / ((lam : ℚ) + 1)) * powIntQ v z ((P : ℤ) + 8) +
    ∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℚ) * (1 / ((lam + 1) * 2 ^ lam)) *
      powIntQ v z ((P : ℤ) + 4 * k - 4 * lam + 4)

/-- The certified partner of cause cell 0. -/
def lcC0 : RSCell := ⟨168179/200000, 840941/1000000, 8, 3, 29, 12190348564073/250000000000000, -4, 60,
  -3085354900612077/1000000000000000⟩

/-- Cause cell 0. -/
def lcc0 : ℚ × ℚ := (499999/1000000, 5001051/10000000)

/-- The upper end of the low window, a fourth power. -/
def lcZ : ℚ := 8408965 / 10000000

/-- The certified per-unit quantity `2 (ub + 403 lowQ) Ex`. -/
def lcQ0 : ℚ := 2 * (lcC0.ub + 403 * lowQ lcC0.v lcZ lcC0.lam lcC0.P) * rsEx lcC0.lu

theorem lc_C0_ok : rsCellOK lcC0 = true := by decide +kernel

theorem lc_link : rsLink lcC0 lcc0 = true := by decide +kernel

theorem lc_cells : cellsXCauseData.all (fun c => decide ((5001 : ℚ) / 10000 ≤ c.1) || decide (c = lcc0)) = true := by
  decide +kernel

theorem lc_z : decide ((1 : ℚ) / 2 + 1 / 10 ^ 7 ≤ lcZ ^ 4) && decide (lcZ ≤ lcC0.w) && decide (lcC0.v ≤ lcZ) &&
    decide (0 ≤ lowQ lcC0.v lcZ lcC0.lam lcC0.P) = true := by decide +kernel

theorem lc_log : (decide (0 < lcQ0) && decide (|1 - crRed lcQ0 (-4)| < 1) &&
    decide (crLnHi lcQ0 (-4) 60 ≤ -30844 / 10000)) = true := by decide +kernel

/-- **`∫_{v⁴}^{z⁴} y^{P/4} gX = lowQ`** (window below the cap). -/
theorem lowQ_eq (v z w : ℚ) (hv : 0 < v) (hvz : v ≤ z) (hzw : z ≤ w) (lam P : ℕ)
    (hk : ∀ k ∈ range (lam + 2), (P : ℤ) + 4 * k - 4 * lam + 4 ≠ 0) (hp : (P : ℤ) + 8 ≠ 0) :
    ∫ y in ((v : ℝ) ^ 4)..((z : ℝ) ^ 4), y ^ ((P : ℝ) / 4) * gX lam ((w : ℝ) ^ 4) y =
      ((lowQ v z lam P : ℚ) : ℝ) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hz0 : 0 < z := lt_of_lt_of_le hv hvz
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz0
  have hab : (v : ℝ) ^ 4 ≤ (z : ℝ) ^ 4 := pow_le_pow_left₀ hv'.le (by exact_mod_cast hvz) 4
  have hbc : (z : ℝ) ^ 4 ≤ (w : ℝ) ^ 4 := pow_le_pow_left₀ hz'.le (by exact_mod_cast hzw) 4
  have hkR : ∀ k ∈ range (lam + 2), (P : ℝ) / 4 + k - lam ≠ -1 := fun k hkm h => by
    apply hk k hkm; have : (((P : ℤ) + 4 * k - 4 * lam + 4 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hpR : (P : ℝ) / 4 + 1 ≠ -1 := fun h => hp (by
    have : (((P : ℤ) + 8 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this)
  rw [integral_below lam (by positivity) hab hbc hkR hpR]
  have e1 : ∀ (a b : ℚ) (m : ℤ) (q : ℝ), 0 < a → 0 < b → q + 1 = (m : ℝ) / 4 →
      powInt ((a : ℝ) ^ 4) ((b : ℝ) ^ 4) q = ((powIntQ a b m : ℚ) : ℝ) :=
    fun a b m q ha hb hq => (powIntQ_cast ha hb m hq).symm
  rw [show powInt ((v : ℝ) ^ 4) ((z : ℝ) ^ 4) ((P : ℝ) / 4 + 1) =
      ((powIntQ v z ((P : ℤ) + 8) : ℚ) : ℝ) from e1 v z ((P : ℤ) + 8) _ hv hz0 (by push_cast; ring)]
  rw [sum_congr rfl fun k _ => show ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
      powInt ((v : ℝ) ^ 4) ((z : ℝ) ^ 4) ((P : ℝ) / 4 + k - lam) =
      ((((lam + 1).choose k : ℚ) * (1 / ((lam + 1) * 2 ^ lam)) *
        powIntQ v z ((P : ℤ) + 4 * k - 4 * lam + 4) : ℚ) : ℝ) from by
    rw [e1 v z ((P : ℤ) + 4 * k - 4 * lam + 4) _ hv hz0 (by push_cast; ring)]
    push_cast; ring]
  unfold lowQ
  push_cast
  ring

/-- **The `J` factor over a window `[c.1, zb]`** (copy of `cell_J_le`). -/
theorem cell_J_le_win (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1)
    {zb : ℝ} (hz : (c.1 : ℝ) ≤ zb) (hz1 : zb ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y ∧ clamp01 y ≤ zb},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        ∫ y in (c.1 : ℝ)..zb, y ^ (t - lamU) * gX lam (c.2 : ℝ) y) := by
  set K := 7 * deltaU N + (slV N + Real.log 2) / N
  set a : ℝ := (c.1 : ℝ)
  have hset : {y : ℝ | a ≤ clamp01 y ∧ clamp01 y ≤ zb} ∩ Set.Icc 0 1 = Set.Icc a zb := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h4⟩, h2, h3⟩
      have : clamp01 y = y := by unfold clamp01; rw [min_eq_right h3, max_eq_right h2]
      exact ⟨this ▸ h1, this ▸ h4⟩
    · rintro ⟨h1, h3⟩
      have h2 : 0 ≤ y := le_trans hm0.le h1
      have h3' : y ≤ 1 := h3.trans hz1
      have : clamp01 y = y := by unfold clamp01; rw [min_eq_right h3', max_eq_right h2]
      refine ⟨⟨?_, ?_⟩, h2, h3'⟩ <;> rw [this] <;> assumption
  have hW : MeasurableSet {y : ℝ | a ≤ clamp01 y ∧ clamp01 y ≤ zb} :=
    (measurableSet_le measurable_const clamp01_measurable).inter
      (measurableSet_le clamp01_measurable measurable_const)
  unfold unif
  rw [Measure.restrict_restrict hW, hset]
  have hcont : ContinuousOn (fun y => Real.exp ((lam : ℝ) * K) * (y ^ (t - lamU) * gX lam (c.2 : ℝ) y))
      (Set.Icc a zb) :=
    continuousOn_const.mul ((ContinuousOn.rpow_const continuousOn_id fun y _ =>
      Or.inr (sub_nonneg.2 hp)).mul ((gX_continuousOn lam _ hm0).mono
        (Set.Icc_subset_Icc le_rfl hz1)))
  calc ∫⁻ y in Set.Icc a zb, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂volume.restrict (Set.Icc 0 1)
      ≤ ∫⁻ y in Set.Icc a zb, ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * gX lam (c.2 : ℝ) y)) := by
        refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hy1 : y ≤ 1 := hy.2.trans hz1
        have hcy : clamp01 y = y := by
          unfold clamp01; rw [min_eq_right hy1, max_eq_right hy0.le]
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
    _ = ENNReal.ofReal (∫ y in Set.Icc a zb, Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * gX lam (c.2 : ℝ) y)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
        refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hy1 : y ≤ 1 := hy.2.trans hz1
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.rpow_nonneg hy0.le _)
          (gX_nonneg lam hy0 hy1 (by linarith) (by linarith)))
    _ = _ := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
          intervalIntegral.integral_const_mul]

/-- **The low-weighted base factor**: `∫_W e^{(λu-t)ℓ} e^{θ 1[y<b]} E e^{-λ g} ≤ e^{λK}(I + (e^θ - 1) I_{[a,zb]})`. -/
theorem lc_ypart (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1)
    (hm1 : (c.1 : ℝ) ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) {bb zb : ℝ} (hbz : bb ≤ zb) (hz : (c.1 : ℝ) ≤ zb)
    (hz1 : zb ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y)) *
          Real.exp (θ * ({y : ℝ | clamp01 y < bb}.indicator (fun _ => (1 : ℝ)) y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        ∫ y in (c.1 : ℝ)..1, y ^ (t - lamU) * gX lam (c.2 : ℝ) y) +
      ENNReal.ofReal (Real.exp θ - 1) *
        ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
          ∫ y in (c.1 : ℝ)..zb, y ^ (t - lamU) * gX lam (c.2 : ℝ) y) := by
  set Ar : ℝ → ℝ := fun y => Real.exp ((lamU - t) * -Real.log (clamp01 y)) with hAr
  set low : Set ℝ := {y : ℝ | clamp01 y < bb} with hlow
  have hL : MeasurableSet low := measurableSet_lt clamp01_measurable measurable_const
  have hWa : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ clamp01 y} := measurableSet_le measurable_const clamp01_measurable
  have hArm : Measurable Ar := Real.measurable_exp.comp
    ((Real.measurable_log.comp clamp01_measurable).neg.const_mul _)
  have hGm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c).const_mul _))
  set IG : ℝ → ENNReal := fun y => ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u)) ∂unif with hIG
  have hIGm : Measurable IG := hGm.lintegral_prod_right'
  have he1 : 0 ≤ Real.exp θ - 1 := by have := Real.add_one_le_exp θ; linarith
  have hpt : ∀ y, ENNReal.ofReal (Ar y * Real.exp (θ * (low.indicator (fun _ => (1 : ℝ)) y))) * IG y =
      ENNReal.ofReal (Ar y) * IG y + low.indicator (fun y => ENNReal.ofReal (Real.exp θ - 1) *
        (ENNReal.ofReal (Ar y) * IG y)) y := by
    intro y
    have hA0 : 0 ≤ Ar y := (Real.exp_pos _).le
    by_cases hy : y ∈ low
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one,
        show Ar y * Real.exp θ = Ar y + (Real.exp θ - 1) * Ar y by ring,
        ENNReal.ofReal_add hA0 (mul_nonneg he1 hA0), ENNReal.ofReal_mul he1, add_mul, mul_assoc]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero, Real.exp_zero, mul_one, add_zero]
  rw [lintegral_congr fun y => hpt y]
  have hm : Measurable fun y => ENNReal.ofReal (Ar y) * IG y := (ENNReal.measurable_ofReal.comp hArm).mul hIGm
  rw [lintegral_add_left hm]
  refine add_le_add (cell_J_le lam c hcm hm0 hm1 hp) ?_
  rw [lintegral_indicator hL, Measure.restrict_restrict hL, lintegral_const_mul _ hm]
  gcongr
  refine le_trans (lintegral_mono_set ?_) (cell_J_le_win lam c hcm hm0 hz hz1 hp)
  rintro y ⟨h1, h2⟩
  exact ⟨h2, le_trans (le_of_lt h1) hbz⟩

/-- **The unit rate of cell 0 with the low weight `e^6`.** -/
theorem lc_unit :
    0 < fsI lcC0 + (Real.exp 6 - 1) *
        ∫ y in ((lcC0.v : ℝ) ^ 4)..((lcZ : ℝ) ^ 4), y ^ ((lcC0.P : ℝ) / 4) * gX lcC0.lam ((lcC0.w : ℝ) ^ 4) y ∧
    Real.log 2 + Real.log (fsI lcC0 + (Real.exp 6 - 1) *
        ∫ y in ((lcC0.v : ℝ) ^ 4)..((lcZ : ℝ) ^ 4), y ^ ((lcC0.P : ℝ) / 4) * gX lcC0.lam ((lcC0.w : ℝ) ^ 4) y) +
      Real.log (rsEx lcC0.lu : ℝ) + ((lcC0.P : ℝ) / 4 + lcC0.lu) * x0 ≤ -(1006 / 1000) := by
  have hok := lc_C0_ok
  have h' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, hk⟩, hp⟩, h0⟩, h1⟩, hub⟩, -⟩, -⟩, -⟩, -⟩ := h'
  have hz := lc_z
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
  obtain ⟨⟨⟨hz4, hzw⟩, hvz⟩, hL0⟩ := hz
  have hI := cellIq_eq lcC0.v lcC0.w hv hvw hw1 lcC0.lam lcC0.P
    (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp h0 h1
  have hIub : fsI lcC0 ≤ (lcC0.ub : ℝ) := by
    unfold fsI; rw [← hI]; exact_mod_cast hub
  have hIpos := fs_cell_pos lcC0 hok
  have hLq := lowQ_eq lcC0.v lcZ lcC0.w hv hvz hzw lcC0.lam lcC0.P
    (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp
  rw [hLq]
  have hL0' : (0 : ℝ) ≤ ((lowQ lcC0.v lcZ lcC0.lam lcC0.P : ℚ) : ℝ) := by exact_mod_cast hL0
  have he6 : Real.exp 6 ≤ 404 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc Real.exp 1 ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 := pow_le_pow_left₀ (Real.exp_pos _).le h.le 6
      _ ≤ 404 := by norm_num
  have he1 : 0 ≤ Real.exp 6 - 1 := by have := Real.add_one_le_exp (6 : ℝ); linarith
  set Lq : ℝ := ((lowQ lcC0.v lcZ lcC0.lam lcC0.P : ℚ) : ℝ) with hLqd
  have hJpos : 0 < fsI lcC0 + (Real.exp 6 - 1) * Lq := by positivity
  refine ⟨hJpos, ?_⟩
  have hJle : fsI lcC0 + (Real.exp 6 - 1) * Lq ≤ ((lcC0.ub + 403 * lowQ lcC0.v lcZ lcC0.lam lcC0.P : ℚ) : ℝ) := by
    push_cast
    nlinarith
  have hEx0 : (0 : ℝ) < rsEx lcC0.lu := by
    have : (0 : ℚ) < rsEx lcC0.lu := by decide +kernel
    exact_mod_cast this
  have hcr := crLog_le (q := lcQ0) (r := -30844 / 10000) (-4) 60 lc_log
  have hsplit : Real.log ((lcQ0 : ℚ) : ℝ) = Real.log 2 +
      Real.log ((lcC0.ub + 403 * lowQ lcC0.v lcZ lcC0.lam lcC0.P : ℚ) : ℝ) + Real.log (rsEx lcC0.lu : ℝ) := by
    have hq : (0 : ℝ) < ((lcC0.ub + 403 * lowQ lcC0.v lcZ lcC0.lam lcC0.P : ℚ) : ℝ) := hJpos.trans_le hJle
    unfold lcQ0
    rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, Real.log_mul (by positivity) hEx0.ne',
      Real.log_mul (by norm_num) hq.ne']
  have hlogJ : Real.log (fsI lcC0 + (Real.exp 6 - 1) * Lq) ≤
      Real.log ((lcC0.ub + 403 * lowQ lcC0.v lcZ lcC0.lam lcC0.P : ℚ) : ℝ) := Real.log_le_log hJpos hJle
  have hx0 := cr_x0_bounds.2
  have ht : ((lcC0.P : ℝ) / 4 + lcC0.lu) * x0 ≤ ((lcC0.P : ℝ) / 4 + lcC0.lu) * (crX0hi : ℝ) :=
    mul_le_mul_of_nonneg_left hx0 (by positivity)
  have hnum : ((lcC0.P : ℝ) / 4 + lcC0.lu) * (crX0hi : ℝ) = 10.25 * (2027325541 / 10000000000) := by
    simp [lcC0, crX0hi]; norm_num
  have hcr' : Real.log ((lcQ0 : ℚ) : ℝ) ≤ -30844 / 10000 := by
    have := hcr; push_cast at this; exact this
  linarith

end Census
end IIT

#print axioms IIT.Census.lc_unit
#print axioms IIT.Census.lc_ypart
