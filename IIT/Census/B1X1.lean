/-
Census, B1 forced joint bound X1 (`JointBound P0X1`), the tightest one (W7 X1', certified 1.010878 vs `RJ = 1.0108`).

On the cause regime, `Σ_{j ≠ x} min(λ_j, log(y_j / cX)) < -N/2000` is excluded by the cause Chernoff template with the
V-sum replaced by the X1 term `g = min(log(2y/(y+u)), log(y/cX)) + 1/2000 - 1/N` (multiplier `λ = 8`), the window
`y ≥ A = 1/2 - 10⁻⁶` (every cause cell has `m_lo ≥ A`), tilt `t = 29/4 + 3`, link `l_u = 3`.

Per unit, `min(a, log(y/cX)) ≥ min(a, max 0 (log(y/c))) + min(log(y/c), 0)` for any cap `c ≥ cX`, so the inner factor
is `≤ e^{λ(1/N - 1/2000)} (c/y)^λ_+ gX λ c y`: exact (`lintegral_mgfX`) above the cap, a constant factor
`(w⁴/v⁴)^λ` on the window `[v⁴, w⁴]` below it.  The `y`-integral is then a combination of two exact cell integrals
(`cellIq`), and the kernel checks `log(2 · ub · Ex) + t x0 - λ/2000 ≤ -R1`, `R1 = 1.01085 > RJ`.
Data: `results/theory/b1cert/x1_lean_cert.py`.
-/
import IIT.Census.CertRSXSound
import IIT.Census.B1ForcedF0

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### Data and kernel checks -/

/-- The window `A = 1/2 - 10⁻⁶`. -/
def x1A : ℚ := 1 / 2 - 1 / 1000000
def x1v : ℚ := 168179 / 200000
def x1w : ℚ := 841737 / 1000000
def x1ub : ℚ := 975684776161 / 20000000000000
def x1r : ℚ := -3084886513633 / 1000000000000
def x1R1 : ℚ := 101085 / 100000

/-- The total `y`-integral (rational): `(w⁴/v⁴)^8 (I(v,w) - I(w,w)) + I(w,w)`. -/
def x1Itot : ℚ :=
  (x1w ^ 4 / x1v ^ 4) ^ 8 * (cellIq x1v x1w 8 29 - cellIq x1w x1w 8 29) + cellIq x1w x1w 8 29

theorem x1_check : (decide (x1Itot ≤ x1ub) && decide (0 < 2 * x1ub * rsEx 3) &&
    decide (|1 - crRed (2 * x1ub * rsEx 3) (-4)| < 1) &&
    decide (crLnHi (2 * x1ub * rsEx 3) (-4) 40 ≤ x1r) &&
    decide (x1r + (29 / 4 + 3) * crX0hi - 8 / 2000 ≤ -x1R1)) = true := by
  decide +kernel

theorem x1_cells : cellsXCauseData.all (fun c => decide (x1A ≤ c.1)) = true := by decide +kernel

lemma x1_vw : (0 : ℚ) < x1v ∧ x1v ≤ x1w ∧ x1w < 1 ∧ x1v ^ 4 ≤ x1A ∧ (251 / 500 : ℚ) ≤ x1w ^ 4 := by
  unfold x1v x1w x1A; norm_num

/-! ### The per-unit X1 term and its inner bound -/

/-- The per-unit X1 term. -/
noncomputable def gX1 (N : ℕ) (y u : ℝ) : ℝ :=
  min (Real.log (2 * clamp01 y / (clamp01 y + clamp01 u))) (Real.log (clamp01 y / cX)) + 1 / 2000 - 1 / N

lemma cX_pos : (0 : ℝ) < cX := by unfold cX; norm_num

lemma min_split_aux (a b b' : ℝ) (hb : b' ≤ b) : min a (max 0 b') + min b' 0 ≤ min a b := by
  rcases le_total 0 b' with h | h
  · rw [max_eq_right h, min_eq_right h, add_zero]; exact min_le_min le_rfl hb
  · rw [max_eq_left h, min_eq_left h]
    refine le_min ?_ ?_
    · linarith [min_le_left a 0]
    · linarith [min_le_right a 0]

/-- **Inner bound**: for `y ∈ (0, 1]` and a cap `c ≥ max(cX, 1/2)`. -/
theorem x1_inner (lam : ℕ) {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) {c : ℝ} (hc2 : 1 / 2 ≤ c) (hcX : cX ≤ c) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gX1 N y u)) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (1 / N - 1 / 2000)) *
        Real.exp (-(lam : ℝ) * min (Real.log (y / c)) 0) * gX lam c y) := by
  have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy1, max_eq_right hy0.le]
  have hc0 : 0 < c := by linarith
  have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  set C := Real.exp ((lam : ℝ) * (1 / N - 1 / 2000)) * Real.exp (-(lam : ℝ) * min (Real.log (y / c)) 0)
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(lam : ℝ) * gX1 N y u) ≤
      C * Real.exp (-(lam : ℝ) * min (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c)))) := by
    intro u hu
    have hcu : clamp01 u = u := by unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]
    have hbb : Real.log (y / c) ≤ Real.log (y / cX) :=
      Real.log_le_log (div_pos hy0 hc0) (div_le_div_of_nonneg_left hy0.le cX_pos hcX)
    have hkey := min_split_aux (Real.log (2 * y / (y + u))) (Real.log (y / cX)) (Real.log (y / c)) hbb
    simp only [C, ← Real.exp_add]
    apply Real.exp_le_exp.2
    unfold gX1
    rw [hcy, hcu]
    nlinarith [mul_le_mul_of_nonneg_left hkey hl]
  calc ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gX1 N y u)) ∂unif
      ≤ ∫⁻ u, ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-(lam : ℝ) *
          min (Real.log (2 * y / (y + u))) (max 0 (Real.log (y / c))))) ∂unif := by
        unfold unif
        refine setLIntegral_mono' measurableSet_Icc fun u hu => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt u hu)
    _ = ENNReal.ofReal C * ENNReal.ofReal (gX lam c y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_mgfX lam hy0 hy1 hc0 (by linarith)]
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-! ### The `y`-integral -/

lemma x1_integrand_cont (lam : ℕ) (c p : ℝ) {a : ℝ} (ha : 0 < a) (hp : 0 ≤ p) :
    ContinuousOn (fun y => y ^ p * gX lam c y) (Set.Icc a 1) :=
  (ContinuousOn.rpow_const continuousOn_id fun _ _ => Or.inr hp).mul (gX_continuousOn lam _ ha)

lemma x1_lint_Icc (lam : ℕ) (c p K : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) (hp : 0 ≤ p)
    (hc : 1 / 2 ≤ c) (hK : 0 ≤ K) :
    ∫⁻ y in Set.Icc a b, ENNReal.ofReal (K * (y ^ p * gX lam c y)) =
      ENNReal.ofReal (K * ∫ y in a..b, y ^ p * gX lam c y) := by
  have hcont : ContinuousOn (fun y => K * (y ^ p * gX lam c y)) (Set.Icc a b) :=
    continuousOn_const.mul ((x1_integrand_cont lam c p ha hp).mono (Set.Icc_subset_Icc le_rfl hb1))
  rw [← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_const_mul]
  · refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (gX_nonneg lam hy0 (hy.2.trans hb1) (by linarith) (by linarith [hy.2.trans hb1])))

/-- **The `J` factor of the X1 template.** -/
theorem x1_J_le (lam : ℕ) {a a0 c : ℝ} (ha0 : 0 < a0) (haa : a0 ≤ a) (ha0c : a0 ≤ c) (hc1 : c ≤ 1)
    (hc2 : 1 / 2 ≤ c) (hcX : cX ≤ c) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | a ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gX1 N y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (1 / N - 1 / 2000)) *
        ((c / a0) ^ lam * (∫ y in a0..c, y ^ (t - lamU) * gX lam c y) +
          ∫ y in c..1, y ^ (t - lamU) * gX lam c y)) := by
  set C := Real.exp ((lam : ℝ) * (1 / N - 1 / 2000)) with hC
  set p := t - lamU with hpdef
  have hp0 : 0 ≤ p := by simp only [hpdef]; linarith
  have hM0 : (0 : ℝ) ≤ (c / a0) ^ lam := by positivity
  have hW : MeasurableSet {y : ℝ | a ≤ clamp01 y} := measurableSet_le measurable_const clamp01_measurable
  set F : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gX1 N y u)) ∂unif with hF
  -- pointwise on `[a0, 1]`
  have hptF : ∀ y ∈ Set.Icc a0 1, F y ≤ ENNReal.ofReal (C * (Real.exp (-(lam : ℝ) *
      min (Real.log (y / c)) 0) * (y ^ p * gX lam c y))) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha0 hy.1
    have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy0.le]
    have hin := x1_inner (N := N) lam hy0 hy.2 hc2 hcX
    have hexp : Real.exp ((lamU - t) * -Real.log (clamp01 y)) = y ^ p := by
      rw [hcy, Real.rpow_def_of_pos hy0]; simp only [hpdef]; ring_nf
    simp only [hF, hexp]
    calc ENNReal.ofReal (y ^ p) * ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gX1 N y u)) ∂unif
        ≤ ENNReal.ofReal (y ^ p) * ENNReal.ofReal (C * Real.exp (-(lam : ℝ) *
            min (Real.log (y / c)) 0) * gX lam c y) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]; congr 1; ring
  -- the factor `e^{-λ min(log(y/c), 0)}`
  have hfac_lo : ∀ y ∈ Set.Icc a0 c, Real.exp (-(lam : ℝ) * min (Real.log (y / c)) 0) ≤ (c / a0) ^ lam := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha0 hy.1
    have hc0 : 0 < c := lt_of_lt_of_le ha0 ha0c
    have h1 : Real.log (a0 / c) ≤ min (Real.log (y / c)) 0 :=
      le_min (Real.log_le_log (div_pos ha0 hc0) (div_le_div_of_nonneg_right hy.1 hc0.le))
        (Real.log_nonpos (div_pos ha0 hc0).le ((div_le_one hc0).2 ha0c))
    calc Real.exp (-(lam : ℝ) * min (Real.log (y / c)) 0) ≤ Real.exp (-(lam : ℝ) * Real.log (a0 / c)) :=
          Real.exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) lam])
      _ = (c / a0) ^ lam := by
          have e : -(lam : ℝ) * Real.log (a0 / c) = Real.log ((c / a0) ^ lam) := by
            rw [Real.log_pow, Real.log_div ha0.ne' (by linarith : c ≠ 0).symm.symm, Real.log_div (by linarith : c ≠ 0) ha0.ne']; ring
          rw [e, Real.exp_log (by positivity)]
  have hfac_hi : ∀ y ∈ Set.Icc c 1, Real.exp (-(lam : ℝ) * min (Real.log (y / c)) 0) = 1 := by
    intro y hy
    have hc0 : 0 < c := lt_of_lt_of_le ha0 ha0c
    rw [min_eq_right (Real.log_nonneg ((one_le_div hc0).2 hy.1)), mul_zero, Real.exp_zero]
  have hgX : ∀ y ∈ Set.Icc a0 1, 0 ≤ y ^ p * gX lam c y := fun y hy => by
    have hy0 : 0 < y := lt_of_lt_of_le ha0 hy.1
    exact mul_nonneg (Real.rpow_nonneg hy0.le _) (gX_nonneg lam hy0 hy.2 (by linarith) (by linarith [hy.2]))
  -- split the domain
  have hset : {y : ℝ | a ≤ clamp01 y} ∩ Set.Icc 0 1 ⊆ Set.Icc a0 c ∪ Set.Icc c 1 := by
    rintro y ⟨hy, h0, h1⟩
    have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right h1, max_eq_right h0]
    simp only [Set.mem_setOf_eq, hcy] at hy
    rcases le_total y c with h | h
    · exact Or.inl ⟨haa.trans hy, h⟩
    · exact Or.inr ⟨h, h1⟩
  unfold unif
  rw [Measure.restrict_restrict hW]
  calc ∫⁻ y in {y : ℝ | a ≤ clamp01 y} ∩ Set.Icc 0 1, F y
      ≤ ∫⁻ y in Set.Icc a0 c ∪ Set.Icc c 1, F y := lintegral_mono_set hset
    _ ≤ (∫⁻ y in Set.Icc a0 c, F y) + ∫⁻ y in Set.Icc c 1, F y := lintegral_union_le _ _ _
    _ ≤ (∫⁻ y in Set.Icc a0 c, ENNReal.ofReal (C * (c / a0) ^ lam * (y ^ p * gX lam c y))) +
          ∫⁻ y in Set.Icc c 1, ENNReal.ofReal (C * (y ^ p * gX lam c y)) := by
        refine add_le_add ?_ ?_
        · refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
          refine (hptF y ⟨hy.1, hy.2.trans hc1⟩).trans (ENNReal.ofReal_le_ofReal ?_)
          have := hgX y ⟨hy.1, hy.2.trans hc1⟩
          have := hfac_lo y hy
          have hC0 : 0 ≤ C := (Real.exp_pos _).le
          calc C * (Real.exp (-(lam : ℝ) * min (Real.log (y / c)) 0) * (y ^ p * gX lam c y))
              = C * Real.exp (-(lam : ℝ) * min (Real.log (y / c)) 0) * (y ^ p * gX lam c y) := by ring
            _ ≤ C * (c / a0) ^ lam * (y ^ p * gX lam c y) := by gcongr
        · refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
          refine (hptF y ⟨ha0c.trans hy.1, hy.2⟩).trans (le_of_eq ?_)
          rw [hfac_hi y hy, one_mul]
    _ = ENNReal.ofReal (C * (c / a0) ^ lam * ∫ y in a0..c, y ^ p * gX lam c y) +
          ENNReal.ofReal (C * ∫ y in c..1, y ^ p * gX lam c y) := by
        rw [x1_lint_Icc lam c p _ ha0 ha0c hc1 hp0 hc2 (by positivity),
          x1_lint_Icc lam c p _ (lt_of_lt_of_le ha0 ha0c) hc1 le_rfl hp0 hc2 (by positivity)]
    _ = _ := by
        have h1 : 0 ≤ ∫ y in a0..c, y ^ p * gX lam c y :=
          intervalIntegral.integral_nonneg ha0c fun y hy => hgX y ⟨hy.1, hy.2.trans hc1⟩
        have h2 : 0 ≤ ∫ y in c..1, y ^ p * gX lam c y :=
          intervalIntegral.integral_nonneg hc1 fun y hy => hgX y ⟨ha0c.trans hy.1, hy.2⟩
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-! ### The event inclusion -/

lemma x1_sub_template (hN : 0 < N) (s r0 : State N) (x : Fin N) :
    {w : Param N | RegEvX N s r0 x .cause w ∧ ¬ P0X1 N s r0 w x .cause} ⊆
      {w | (∀ i, w ((fun _ : Fin N => r0) i) i ∈ {y : ℝ | ((x1A : ℚ) : ℝ) ≤ clamp01 y}) ∧
        ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ≤ x0 * N + slT N ∧
        ∑ i, ellUX N (w ((fun _ : Fin N => s) i) i) ≤
          ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, gX1 N (w ((fun _ : Fin N => r0) i) i) (w ((fun _ : Fin N => flipAt x r0) i) i) ≤ 0} := by
  rintro w ⟨⟨c, hc, h1, -, h3, h4, -, -⟩, hn⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcA : ((x1A : ℚ) : ℝ) ≤ c.1 := by
    have := (List.all_eq_true.1 x1_cells) c (by simpa [cellsX] using hc)
    simp only [decide_eq_true_eq] at this
    exact_mod_cast this
  have hA0 : (0 : ℝ) < ((x1A : ℚ) : ℝ) := by unfold x1A; norm_num
  refine ⟨fun i => hcA.trans (h1 i), h3, ?_, ?_⟩
  · have : ∑ i, ellUX N (w s i) = ∑ k, -Real.log (xE w s k) - slT N := by
      simp only [ellUX, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hNr.ne']
      rfl
    show ∑ i, ellUX N (w s i) ≤ ∑ i, -Real.log (clamp01 (w r0 i))
    rw [this]
    have hX : XW w r0 = ∑ i, -Real.log (clamp01 (w r0 i)) := rfl
    linarith
  · simp only [P0X1, forall_const, not_le] at hn
    set m : Fin N → ℝ := fun j => min (Real.log (2 * clamp01 (w r0 j) /
      (clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j)))) (Real.log (clamp01 (w r0 j) / cX)) with hm
    have hmj : ∀ j ∈ univ.erase x, min (lamX w s r0 x .cause j) (Real.log (clamp01 (w r0 j) / cX)) = m j := by
      intro j _; rfl
    rw [Finset.sum_congr rfl hmj] at hn
    have hmx : m x ≤ 1 := by
      have hy0 : 0 < clamp01 (w r0 x) := lt_of_lt_of_le hA0 (hcA.trans (h1 x))
      have h2 : Real.log (clamp01 (w r0 x) / cX) ≤ 1 := by
        have hle : clamp01 (w r0 x) / cX ≤ Real.exp 1 := by
          rw [div_le_iff₀ cX_pos]
          have := clamp01_le_one (w r0 x)
          have := Real.add_one_le_exp 1
          unfold cX; nlinarith
        calc Real.log (clamp01 (w r0 x) / cX) ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (div_pos hy0 cX_pos) hle
          _ = 1 := Real.log_exp 1
      exact (min_le_right _ _).trans h2
    have hsum : ∑ i, gX1 N (w r0 i) (w (flipAt x r0) i) = ∑ i, m i + N * (1 / 2000) - 1 := by
      simp only [gX1, hm, sum_sub_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    show ∑ i, gX1 N (w r0 i) (w (flipAt x r0) i) ≤ 0
    rw [hsum, ← add_sum_erase _ _ (mem_univ x)]
    have : (N : ℝ) * (1 / 2000) = N / 2000 := by ring
    linarith

/-! ### The joint bound -/

lemma x1_absorb : ∀ᶠ N : ℕ in atTop,
    Real.exp (8 + (29 / 4 + 3 + 3) * slT N) ≤ Real.exp (((x1R1 : ℝ) - RJ) * N) := by
  have hab := poly_absorb 1 0 (δ := (x1R1 : ℝ) - RJ) (by unfold x1R1 RJ; norm_num)
  filter_upwards [hab, eventually_ge_atTop 1] with N hab hN1
  refine le_trans (Real.exp_le_exp.2 ?_) (by simpa using hab)
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  unfold slT; nlinarith

/-- **`JointBound P0X1`, PROVED** (rate `≥ 1.01085 > RJ`). -/
theorem joint_x1_proved : JointBound P0X1 := by
  filter_upwards [x1_absorb, eventually_ge_atTop 7] with N hab hN7 s r0 x σ hfar
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  cases σ with
  | effect =>
    have : {w : Param N | RegEvX N s r0 x .effect w ∧ ¬ P0X1 N s r0 w x .effect} = ∅ := by
      ext w; simp [P0X1]
    rw [this, measure_empty]; exact zero_le
  | cause =>
  -- rows
  have hh0 := ham_flipAt_le_one x r0
  have hr0s : r0 ≠ s := by intro h; rw [h, ham_self] at hfar; omega
  have hr1s : flipAt x r0 ≠ s := by
    intro h
    have t1 := ham_triangle r0 (flipAt x r0) s
    rw [h, ham_self] at t1
    have : ham r0 (flipAt x r0) ≤ 1 := by rw [ham_comm]; exact hh0
    rw [h] at this
    omega
  -- data
  obtain ⟨hv0, hvw, hw1, hv4, hw4⟩ := x1_vw
  have hc := x1_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hub, hq0⟩, hq⟩, hlnhi⟩, hrate⟩ := hc
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = (x1v : ℝ) := ⟨_, rfl⟩
  obtain ⟨wq, hwdef⟩ : ∃ wq : ℝ, wq = (x1w : ℝ) := ⟨_, rfl⟩
  have hv0' : 0 < v := by rw [hvdef]; exact_mod_cast hv0
  have hw0' : 0 < wq := by rw [hwdef]; exact_mod_cast (lt_of_lt_of_le hv0 hvw)
  have hvw' : v ≤ wq := by rw [hvdef, hwdef]; exact_mod_cast hvw
  have hw1r : wq < 1 := by rw [hwdef]; exact_mod_cast hw1
  have hv4w4 : v ^ 4 ≤ wq ^ 4 := pow_le_pow_left₀ hv0'.le hvw' 4
  have hw41 : wq ^ 4 ≤ 1 := pow_le_one₀ hw0'.le hw1r.le
  have hw4X : cX ≤ wq ^ 4 := by
    have := (Rat.cast_le (K := ℝ)).2 hw4; push_cast at this; rw [hwdef]; unfold cX; linarith
  have hw42 : (1 : ℝ) / 2 ≤ wq ^ 4 := by
    have : (1 : ℝ) / 2 ≤ cX := by unfold cX; norm_num
    linarith
  have hvA : v ^ 4 ≤ ((x1A : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hv4; push_cast at this ⊢; rw [hvdef]; exact this
  set t : ℝ := 29 / 4 + 3 with htdef
  set K1 : ℝ := 1 / N - 1 / 2000 with hK1
  set I1 := ∫ y in (v ^ 4)..(wq ^ 4), y ^ (t - 3) * gX 8 (wq ^ 4) y with hI1
  set I2 := ∫ y in (wq ^ 4)..1, y ^ (t - 3) * gX 8 (wq ^ 4) y with hI2
  set M : ℝ := (wq ^ 4 / v ^ 4) ^ 8 with hM
  set Ireal : ℝ := M * I1 + I2 with hIreal
  set Ex : ℝ := Real.exp ((3 : ℝ) * (slT N / N)) * (2 * (1 - (1 / 2 : ℝ) ^ (3 + 1)) / (3 + 1)) with hEx
  have hgX0 : ∀ y ∈ Set.Icc (v ^ 4) 1, 0 ≤ y ^ (t - 3) * gX 8 (wq ^ 4) y := fun y hy => by
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
    exact mul_nonneg (Real.rpow_nonneg hy0.le _) (gX_nonneg 8 hy0 hy.2 (by linarith) (by linarith [hy.2]))
  have hI10 : 0 ≤ I1 := intervalIntegral.integral_nonneg hv4w4 fun y hy => hgX0 y ⟨hy.1, hy.2.trans hw41⟩
  have hI2pos : 0 < I2 := by
    have hw1' : wq ^ 4 < 1 := pow_lt_one₀ hw0'.le hw1r (by norm_num)
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun y hy => ?_) hw1'
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hw1'.le]
      exact x1_integrand_cont 8 _ _ (by positivity) (by simp only [htdef]; norm_num)
    · have hy0 : 0 < y := lt_trans (by positivity) hy.1
      refine mul_pos (Real.rpow_pos_of_pos hy0 _) (gX_pos 8 hy0 hy.2.le (by linarith) ?_)
      linarith [hy.2]
  have hIpos : 0 < Ireal := by simp only [hIreal]; positivity
  -- the template
  have hJ := x1_J_le (N := N) 8 (a := ((x1A : ℚ) : ℝ)) (a0 := v ^ 4) (c := wq ^ 4) (by positivity) hvA
    hv4w4 hw41 hw42 hw4X (t := t) (lamU := 3) (by simp only [htdef]; norm_num)
  have hE := lintegral_ellUX (N := N) 3
  have hellU : Measurable (ellUX N) := by
    unfold ellUX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  have hg : Measurable fun p : ℝ × ℝ => gX1 N p.1 p.2 := by
    unfold gX1
    have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
    have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
    refine ((Measurable.min ?_ ?_).add_const _).sub_const _
    · exact Real.measurable_log.comp ((measurable_const.mul hy).div (hy.add hu))
    · exact Real.measurable_log.comp (hy.div_const _)
  have hJ0 : 0 ≤ Real.exp ((8 : ℕ) * K1) * Ireal := by positivity
  have hEx0 : 0 ≤ Ex := by simp only [hEx]; norm_num; positivity
  have hmain := joint_template_real (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => hr0s) (fun _ => hr1s)
    (fun y => -Real.log (clamp01 y)) (ellUX N) (gX1 N)
    (Real.measurable_log.comp clamp01_measurable).neg hellU hg _
    (measurableSet_le measurable_const clamp01_measurable)
    (x0 * N + slT N) t 3 (8 : ℕ) (by simp only [htdef]; norm_num) (by norm_num) (Nat.cast_nonneg _)
    hJ0 hEx0 (by simpa [hK1, hIreal, hM] using hJ) (by simpa [hEx] using hE.le)
  refine (measure_mono (x1_sub_template hN s r0 x)).trans (hmain.trans (ENNReal.ofReal_le_ofReal ?_))
  -- the rate
  have hIeq : Ireal = ((x1Itot : ℚ) : ℝ) := by
    have hk : ∀ k ∈ range (8 + 2), (29 : ℤ) + 4 * k - 4 * 8 + 4 ≠ 0 := by
      intro k _; omega
    have e1 := cellIq_eq x1v x1w hv0 hvw hw1.le 8 29 hk (by norm_num) (by norm_num) (by norm_num)
    have e2 := cellIq_eq x1w x1w (lt_of_lt_of_le hv0 hvw) le_rfl hw1.le 8 29 hk (by norm_num)
      (by norm_num) (by norm_num)
    have hp : ((29 : ℕ) : ℝ) / 4 = t - 3 := by simp only [htdef]; norm_num
    rw [hp] at e1 e2
    have hint : ∀ a b : ℝ, v ^ 4 ≤ a → a ≤ 1 → v ^ 4 ≤ b → b ≤ 1 →
        IntervalIntegrable (fun y => y ^ (t - 3) * gX 8 (wq ^ 4) y) volume a b := by
      intro a b ha ha1 hb hb1
      refine ContinuousOn.intervalIntegrable ((x1_integrand_cont 8 _ _ (a := v ^ 4) (by positivity)
        (by simp only [htdef]; norm_num)).mono ?_)
      intro y hy
      rcases Set.mem_uIcc.1 hy with h | h
      · exact ⟨ha.trans h.1, h.2.trans hb1⟩
      · exact ⟨hb.trans h.1, h.2.trans ha1⟩
    have hsplit : I1 + I2 = ∫ y in (v ^ 4)..1, y ^ (t - 3) * gX 8 (wq ^ 4) y :=
      intervalIntegral.integral_add_adjacent_intervals (hint _ _ le_rfl (hv4w4.trans hw41) hv4w4 hw41)
        (hint _ _ hv4w4 hw41 (hv4w4.trans hw41) le_rfl)
    simp only [x1Itot]
    push_cast
    simp only [← hvdef, ← hwdef] at e1 e2 ⊢
    rw [e1, e2, ← hsplit]
    simp only [hIreal, hM]
    ring
  have hlogI : Real.log Ireal ≤ Real.log (x1ub : ℝ) :=
    Real.log_le_log hIpos (by rw [hIeq]; exact_mod_cast hub)
  have hub0 : (0 : ℝ) < x1ub := lt_of_lt_of_le hIpos (by rw [hIeq]; exact_mod_cast hub)
  have hrsEx : ((rsEx 3 : ℚ) : ℝ) = 2 * (1 - (1 / 2 : ℝ) ^ (3 + 1)) / (3 + 1) := by
    unfold rsEx; push_cast; ring
  have hEx3 : (0 : ℝ) < 2 * (1 - (1 / 2 : ℝ) ^ (3 + 1)) / (3 + 1) := by norm_num
  have hcr := crLog_le (q := 2 * x1ub * rsEx 3) (r := x1r) (-4) 40 (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq0, hq⟩, hlnhi⟩)
  have hsplitL : Real.log (((2 * x1ub * rsEx 3 : ℚ)) : ℝ) =
      Real.log 2 + Real.log (x1ub : ℝ) + Real.log (2 * (1 - (1 / 2 : ℝ) ^ (3 + 1)) / (3 + 1)) := by
    push_cast
    rw [← hrsEx, Real.log_mul (by positivity) (by rw [hrsEx]; exact hEx3.ne'),
      Real.log_mul (by norm_num) hub0.ne']
  have hx0 := cr_x0_bounds.2
  have hrR : ((x1r : ℚ) : ℝ) + (29 / 4 + 3) * (crX0hi : ℝ) - 8 / 2000 ≤ -(x1R1 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this ⊢; linarith
  have hlog : Real.log 2 + Real.log Ireal + Real.log (2 * (1 - (1 / 2 : ℝ) ^ (3 + 1)) / (3 + 1)) +
      t * x0 ≤ -((x1R1 : ℝ) - 1 / 250) := by
    have ht0 : (0 : ℝ) ≤ t := by simp only [htdef]; norm_num
    have := mul_le_mul_of_nonneg_left hx0 ht0
    simp only [htdef] at this ⊢
    linarith
  have hrate' := rate_of_log_le hIpos hEx3 hlog N
  -- assemble
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hK1N : ((8 : ℕ) : ℝ) * K1 * N = 8 - N / 250 := by
    simp only [hK1]; field_simp; ring
  have e : Real.exp (t * (x0 * N + slT N)) * (Real.exp ((8 : ℕ) * K1) * Ireal * Ex) ^ N =
      (2 ^ N * (Real.exp (t * (x0 * N)) * (Ireal * (2 * (1 - (1 / 2 : ℝ) ^ (3 + 1)) / (3 + 1))) ^ N)) *
        (Real.exp (-(N : ℝ) / 250) * Real.exp (8 + (t + 3) * slT N)) / 2 ^ N := by
    have ea : (Real.exp ((8 : ℕ) * K1)) ^ N = Real.exp (8 - N / 250) := by
      rw [← Real.exp_nat_mul, ← hK1N]; ring_nf
    have eb : (Real.exp ((3 : ℝ) * (slT N / N))) ^ N = Real.exp (3 * slT N) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    simp only [hEx]
    rw [mul_pow, mul_pow, mul_pow, ea, eb]
    rw [show Real.exp (t * (x0 * N + slT N)) = Real.exp (t * (x0 * N)) * Real.exp (t * slT N) by
      rw [← Real.exp_add]; ring_nf]
    rw [show Real.exp (-(N : ℝ) / 250) * Real.exp (8 + (t + 3) * slT N) =
        Real.exp (8 - N / 250) * Real.exp (3 * slT N) * Real.exp (t * slT N) by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf]
    field_simp
    ring
  rw [e, div_le_div_iff_of_pos_right h2N]
  have hexp1 : Real.exp (-(((x1R1 : ℝ) - 1 / 250) * N)) * Real.exp (-(N : ℝ) / 250) =
      Real.exp (-((x1R1 : ℝ) * N)) := by
    rw [← Real.exp_add]; ring_nf
  calc (2 ^ N * (Real.exp (t * (x0 * N)) * (Ireal * (2 * (1 - (1 / 2 : ℝ) ^ (3 + 1)) / (3 + 1))) ^ N)) *
        (Real.exp (-(N : ℝ) / 250) * Real.exp (8 + (t + 3) * slT N))
      ≤ Real.exp (-(((x1R1 : ℝ) - 1 / 250) * N)) *
          (Real.exp (-(N : ℝ) / 250) * Real.exp (8 + (t + 3) * slT N)) :=
        mul_le_mul_of_nonneg_right hrate' (by positivity)
    _ = Real.exp (-((x1R1 : ℝ) * N)) * Real.exp (8 + (t + 3) * slT N) := by rw [← hexp1]; ring
    _ ≤ Real.exp (-((x1R1 : ℝ) * N)) * Real.exp (((x1R1 : ℝ) - RJ) * N) :=
        mul_le_mul_of_nonneg_left (by simpa [htdef] using hab) (Real.exp_pos _).le
    _ = Real.exp (-(RJ * N)) := by rw [← Real.exp_add]; ring_nf

end Census
end IIT

#print axioms IIT.Census.joint_x1_proved
